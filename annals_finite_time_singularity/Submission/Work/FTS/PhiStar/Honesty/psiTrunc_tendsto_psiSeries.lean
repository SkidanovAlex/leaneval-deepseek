import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiBox
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSolR.PerModeInner
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Slots
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Aux.R.DthIbp
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.FTS_EllLimOK.PkgJets.pinHardy
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The properties of the logarithmic cut-off family that the core proof uses (these are
exactly the conclusions of `Work.EllipticEst.Core.zLogCut`). -/
structure CutFam (χ : ℕ → ℝ → ℝ) (K : ℝ) : Prop where
  K0 : 0 ≤ K
  sm : ∀ (k : ℕ), ContDiffOn ℝ Work.Stability.smoothOrder (χ k) (Set.Ioi 0)
  bnd : ∀ (k : ℕ) (z : ℝ), 0 < z → 0 ≤ χ k z ∧ χ k z ≤ 1
  supp : ∀ (k : ℕ) (z : ℝ), 0 < z → (z ≤ 1 / ((k : ℝ) + 1) ^ 2 ∨ ((k : ℝ) + 1) ^ 2 ≤ z) → χ k z = 0
  mono : ∀ (k : ℕ) (z : ℝ), 0 < z → χ k z ≤ χ (k + 1) z
  conv : ∀ (z : ℝ), 0 < z → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 1 - χ k z < ε
  d1 : ∀ (k : ℕ) (z : ℝ), 0 < z → |z * deriv (χ k) z| ≤ K / Real.log ((k : ℝ) + 2)
  d2 : ∀ (k : ℕ) (z : ℝ), 0 < z →
    |z * deriv (fun y : ℝ => y * deriv (χ k) y) z| ≤ K / Real.log ((k : ℝ) + 2)

theorem cutFam_exists : ∃ (χ : ℕ → ℝ → ℝ) (K : ℝ), CutFam χ K := by
  obtain ⟨χ, K, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Work.EllipticEst.Core.zLogCut
  exact ⟨χ, K, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The support window of `χ k`: `[a_k, b_k]`. -/
def cA (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1) ^ 2
def cB (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2

theorem cA_pos (k : ℕ) : 0 < cA k := by
  rw [cA]; positivity

theorem cA_le_cB (k : ℕ) : cA k ≤ cB k := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
  have h2 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
  rw [cA, cB, div_le_iff₀ h2]
  nlinarith [h1, sq_nonneg ((k : ℝ) + 1 - 1)]

theorem cB_pos (k : ℕ) : 0 < cB k := by
  rw [cB]; positivity


/-! ## The cut-off quantities of the `m`-level argument

For a (smooth) `ψ : ℝ → ℝ → ℝ` and the cut-off index `k` we abbreviate the four parameter
integrals over the window `[cA k, cB k]`:

* `cMK χ k ψ θ  = ∫ χ_k w² ψ²`      (the cut-off mass `m_k(θ)`),
* `cPK χ k ψ θ  = ∫ χ_k w² ψ ∂_θψ`   (`= m_k'(θ)/2`),
* `cAK χ k ψ θ  = ∫ χ_k w² (∂_θψ)²`  (the `θ`-energy, `X_k` before integration in `θ`),
* `cBK χ k ψ θ  = ∫ χ_k w² ψ ∂_θ²ψ`  (the pairing; `m_k''/2 = AK + BK`).

The Cauchy–Schwarz bound `PK² ≤ MK·AK` is what makes `g_k := √m_k` satisfy `(g_k')² ≤ AK`.
-/

/-- The cut-off mass `m_k(θ) = ∫ χ_k w² ψ²`. -/
def cMK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ ^ 2

/-- The cut-off cross term `P_k(θ) = ∫ χ_k w² ψ ∂_θψ` (half of `m_k'`). -/
def cPK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ

/-- `A_k(θ) = ∫ χ_k w² (∂_θψ)²`, the first half of `m_k''/2`. -/
def cAK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ) ^ 2

/-- `B_k(θ) = ∫ χ_k w² ψ ∂_θ²ψ`, the second half of `m_k''/2`. -/
def cBK (χ : ℕ → ℝ → ℝ) (k : ℕ) (ψ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pthIter 2 ψ z θ

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllSol.RPAe.groupBoundF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.RPAe

/-!
# The per-`z` comparison of the slice groups of `f` and `∂_θ² f`

For `f` of class `C^∞` on the open quadrant, `z > 0` and `j ≤ 4`, the `j`-th slice group of `f`
is dominated by the `j`-th slice group of `∂_θ² f`, up to the universal constant `sliceCs`:

`∫_Iθ sliceGroup α 4 j f z θ ≤ sliceCs · ∫_Iθ sliceGroup α 4 j (∂_θ² f) z θ`.

ROUTE.  Both groups are, on the open interval, `(w z)²` times a *single-slice* functional of the
`j`-th radial slice of `f`:

* `sliceGroup α 4 j f z θ = (w z)² · sliceW (4-j) α u θ` where `u = θ' ↦ D_z^j f z θ'`
  (`VopAux.sliceGroup_eq_sliceW`), and
* `sliceGroup α 4 j (∂_θ² f) z θ = (w z)² · sliceW (4-j) α u'' θ`
  (`VopAux.sliceGroup_eq_sliceW` for `∂_θ²f` + `VopAux.sliceW_pthIter2_eq_sliceW_sliceV`).

Since `Iθ` and the open interval differ by the two null endpoints, the two integral identities
follow from the pointwise identities (`EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo`) and the
constant `(w z)²` comes out of the integral (`MeasureTheory.integral_const_mul`).  The remaining
inequality `sliceF (4-j) α u ≤ C · sliceF (4-j) α u''` is the one-dimensional `∂_θ²`-Poincaré
estimate with traces `VopAux.sliceF_le_sliceV_apply`, whose integrability hypotheses on the data
`u''` are supplied by `VopAux.integrableOn_sliceV_thEta` / `VopAux.integrableOn_sliceV_LopIter`
from the assumed integrability of `HkIntegrand α 4 (∂_θ² f)`.  Finally
`C = Classical.choose (VopAux.sliceF_le_sliceV (4-j)) ≤ sliceCs` (`RPAe.le_sliceCs_F`) and
`sliceF (4-j) α u'' ≥ 0` (`VopAux.sliceF_nonneg`) finish the estimate.
-/

theorem groupBoundF : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f →
    ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ 4 →
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) := by
  intro α f hα0 hα1 hf z hz j hj hlim0 hlim1 hint
  -- the raw `∀ n` shape of the smoothness hypothesis, on the open quadrant
  have hfQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hf.forall
  have hpth2Q : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := hf.pth.pth.forall
    intro n
    exact h n
  -- the `j`-th radial slice of `f`, as a function of `θ`
  have hUsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' => Work.Spaces.DzIter j f z θ')
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.VopAux.contDiffOn_slice_of_smoothOpen (hf.DzIter j) hz
  -- integrability of the data `u''` and of its angular derivatives
  have hintV : MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllSol.VopAux.integrableOn_sliceV_thEta (α := α) (k := 4) (f := f) hf hz hj hint
  have hintVm : ∀ m ∈ Finset.Icc 1 (4 - j), MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact Work.FTS.EllSol.VopAux.integrableOn_sliceV_LopIter (α := α) (k := 4) (f := f) hf hz
      hm1 (by omega) hint
  -- the one-dimensional `∂_θ²`-Poincaré estimate on the slice
  have hslice : Work.FTS.EllSol.VopAux.sliceF (4 - j) α
        (fun θ' => Work.Spaces.DzIter j f z θ')
      ≤ Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) *
        Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
    (Work.FTS.EllSol.RPAe.sliceF_le_sliceV_apply (4 - j) α
      (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1 hUsmooth hlim0 hlim1 hintV hintVm).2.2
  -- the two pointwise identities, on the open interval
  have hL : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
              (fun θ' => Work.Spaces.DzIter j f z θ') θ :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (f := fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      (g := fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
        (fun θ' => Work.Spaces.DzIter j f z θ') θ)
      (fun θ hθ => Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j f hz hfQ θ hθ)
  have hR : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pthIter 2 f) z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (f := fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
      (g := fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
      (fun θ hθ => by
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j (Work.Spaces.pthIter 2 f) hz
            hpth2Q θ hθ,
          Work.FTS.EllSol.VopAux.sliceW_pthIter2_eq_sliceW_sliceV α (4 - j) j f hz hfQ θ hθ])
  -- both integrals are `(w z)²` times the corresponding `sliceF`
  have hLint : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (fun θ' => Work.Spaces.DzIter j f z θ') := by
    rw [Work.FTS.EllSol.VopAux.sliceF, hL, MeasureTheory.integral_const_mul]
  have hRint : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pthIter 2 f) z θ)
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
    rw [Work.FTS.EllSol.VopAux.sliceF, hR, MeasureTheory.integral_const_mul]
  -- the constant produced by the one-dimensional estimate is dominated by `sliceCs`
  have hC : Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) ≤ sliceCs :=
    le_sliceCs_F (4 - j) (by omega)
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllSol.VopAux.sliceF_nonneg (4 - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')))
  rw [hLint, hRint]
  calc (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
        (fun θ' => Work.Spaces.DzIter j f z θ')
      ≤ (Work.Spaces.w z) ^ 2 *
          (Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) *
            Work.FTS.EllSol.VopAux.sliceF (4 - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
        mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
    _ = Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) *
          ((Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
        ring
    _ ≤ sliceCs * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
        mul_le_mul_of_nonneg_right hC hX0

end Work.FTS.EllSol.RPAe
end
-- ===== merged: Submission.Work.FTS.EllSol.RPAe.groupBoundP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.RPAe

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The per-`z` comparison of the slice groups of `∂_θ f` and `∂_θ² f`

For `f` of class `C^∞` on the open quadrant, `z > 0` and `j ≤ 4`, the `j`-th slice group of
`∂_θ f` is dominated by the `j`-th slice group of `∂_θ² f`, up to the universal constant
`sliceCs`:

`∫_Iθ sliceGroup α 4 j (∂_θ f) z θ ≤ sliceCs · ∫_Iθ sliceGroup α 4 j (∂_θ² f) z θ`.

ROUTE.  Both groups are, on the open interval, `(w z)²` times a *single-slice* functional of the
`j`-th radial slice of `f`:

* `sliceGroup α 4 j (∂_θ f) z θ = (w z)² · sliceW (4-j) α (u') θ` where `u = θ' ↦ D_z^j f z θ'`
  (`VopAux.sliceGroup_pth_eq_sliceW`), and
* `sliceGroup α 4 j (∂_θ² f) z θ = (w z)² · sliceW (4-j) α (u'') θ`
  (`VopAux.sliceGroup_eq_sliceW` + `VopAux.sliceW_pthIter2_eq_sliceW_sliceV`).

Since `Iθ` and the open interval differ by the two null endpoints, the two integral identities
follow from the pointwise identities (`EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo`) and the
constant `(w z)²` comes out of the integral (`MeasureTheory.integral_const_mul`).  The remaining
inequality `sliceF (4-j) α u' ≤ C · sliceF (4-j) α u''` is the one-dimensional `∂_θ`-Poincaré
estimate with traces `VopAux.sliceF_deriv_le_sliceV_apply`, whose integrability hypotheses on the
data `u''` are supplied by `VopAux.integrableOn_sliceV_thEta` /
`VopAux.integrableOn_sliceV_LopIter` from the assumed integrability of `HkIntegrand α 4 (∂_θ² f)`.
Finally `C = Classical.choose (VopAux.sliceF_deriv_le_sliceV (4-j)) ≤ sliceCs`
(`RPAe.le_sliceCs_D`) and `sliceF (4-j) α u'' ≥ 0` (`VopAux.sliceF_nonneg`) finish the estimate.
-/

theorem groupBoundP : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f →
    ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ 4 →
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ)
      ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) := by
  intro α f hα0 hα1 hf z hz j hj hlim0 hlim1 hint
  -- the raw `∀ n` shape of the smoothness hypothesis, on the open quadrant
  have hfQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hf.forall
  have hpth2Q : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := hf.pth.pth.forall
    intro n
    exact h n
  -- the `j`-th radial slice of `f`, as a function of `θ`
  have hUsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' => Work.Spaces.DzIter j f z θ')
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.VopAux.contDiffOn_slice_of_smoothOpen (hf.DzIter j) hz
  -- integrability of the data `u''` and of its angular derivatives
  have hintV : MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllSol.VopAux.integrableOn_sliceV_thEta (α := α) (k := 4) (f := f) hf hz hj hint
  have hintVm : ∀ m ∈ Finset.Icc 1 (4 - j), MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact Work.FTS.EllSol.VopAux.integrableOn_sliceV_LopIter (α := α) (k := 4) (f := f) hf hz
      hm1 (by omega) hint
  -- the one-dimensional `∂_θ`-Poincaré estimate on the slice
  have hslice : Work.FTS.EllSol.VopAux.sliceF (4 - j) α
        (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
      ≤ Classical.choose (Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV (4 - j)) *
        Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
    (Work.FTS.EllSol.RPAe.sliceF_deriv_le_sliceV_apply (4 - j) α
      (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1 hUsmooth hlim0 hlim1 hintV hintVm).2.2
  -- the two pointwise identities, on the open interval
  have hL : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pth f) z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
              (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (f := fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ)
      (g := fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ)
      (fun θ hθ => Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW α 4 j f hz hfQ θ hθ)
  have hR : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pthIter 2 f) z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (f := fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
      (g := fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
      (fun θ hθ => by
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j (Work.Spaces.pthIter 2 f) hz
            hpth2Q θ hθ,
          Work.FTS.EllSol.VopAux.sliceW_pthIter2_eq_sliceW_sliceV α (4 - j) j f hz hfQ θ hθ])
  -- both integrals are `(w z)²` times the corresponding `sliceF`
  have hLint : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pth f) z θ)
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) := by
    rw [Work.FTS.EllSol.VopAux.sliceF, hL, MeasureTheory.integral_const_mul]
  have hRint : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pthIter 2 f) z θ)
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
    rw [Work.FTS.EllSol.VopAux.sliceF, hR, MeasureTheory.integral_const_mul]
  -- the constant produced by the one-dimensional estimate is dominated by `sliceCs`
  have hC : Classical.choose (Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV (4 - j)) ≤ sliceCs :=
    le_sliceCs_D (4 - j) (by omega)
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllSol.VopAux.sliceF_nonneg (4 - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')))
  rw [hLint, hRint]
  calc (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
        (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
      ≤ (Work.Spaces.w z) ^ 2 *
          (Classical.choose (Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV (4 - j)) *
            Work.FTS.EllSol.VopAux.sliceF (4 - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
        mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
    _ = Classical.choose (Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV (4 - j)) *
          ((Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
        ring
    _ ≤ sliceCs * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
        mul_le_mul_of_nonneg_right hC hX0

end Work.FTS.EllSol.RPAe
end
-- ===== merged: Submission.Work.FTS.EllSol.RPAe.sliceSqEtaInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.RPAe

set_option autoImplicit false

/-- The open interval `(0, π/2)` has finite Lebesgue measure. -/
theorem volume_Ioo_lt_top : (volume : Measure ℝ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≠ ⊤ := by
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- The weight `thEta θ = sin(2θ)^{-η}` is at least `1` on the open interval. -/
theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ :=
  Work.FTS.EllipticEst.H2W.one_le_sEta hθ

/-- The weight `thEta` is nonnegative on `Iθ`. -/
theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

/-- The weight `thEta` is continuous on the open interval. -/
theorem continuousOn_thEta : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  fun θ hθ => (Work.FTS.EllipticEst.H2W.continuousAt_sEta hθ).continuousWithinAt

/-- **Trace-free endpoint control.**  If `u` is `C^∞` on the open interval `(0, π/2)` and
`∫_{Iθ} (u'')² sin(2θ)^{-η} < ∞`, then `u² sin(2θ)^{-η}` and `(u')² sin(2θ)^{-η}` are integrable
on `Iθ`. -/
theorem sliceBdd_of_sq_sliceV {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hIoo : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hIooMeas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have haeMem : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ae_restrict_mem hIooMeas
  -- smoothness of `u'` and of `u''` on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ContDiffOn.deriv_of_isOpen (hu 2) isOpen_Ioo (by norm_cast)
  have hd0 : ContDiffOn ℝ 0 (Work.FTS.EllipticEst.sliceV u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := ContDiffOn.deriv_of_isOpen hd1 isOpen_Ioo (m := 0) (by norm_cast)
    simpa only [Work.FTS.EllipticEst.sliceV] using h
  -- `(u'')²` is integrable on the open interval
  have hA' : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    show MeasureTheory.Integrable _
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    rw [hIoo]
    exact hA
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hA'
      ((hd0.continuousOn.pow 2).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
    rw [Real.norm_of_nonneg (sq_nonneg (Work.FTS.EllipticEst.sliceV u θ))]
    calc (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        = (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- `u''` is integrable on the open interval
  have hA1 : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.sliceV u)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono'
      (g := fun θ => (1 / 2) * ((Work.FTS.EllipticEst.sliceV u θ) ^ 2 + 1))
      ((hA2.add (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
        volume_Ioo_lt_top)).const_mul (1 / 2))
      (hd0.continuousOn.aestronglyMeasurable hIooMeas) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    have h2 : |Work.FTS.EllipticEst.sliceV u θ|
        ≤ (1 / 2) * ((Work.FTS.EllipticEst.sliceV u θ) ^ 2 + 1) := by
      nlinarith [sq_nonneg (|Work.FTS.EllipticEst.sliceV u θ| - 1),
        sq_abs (Work.FTS.EllipticEst.sliceV u θ)]
    exact h2
  -- `deriv u` is bounded on the open interval
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv hpi
      (φ := deriv u)
      (fun θ hθ => (((hd1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt))
      (by simpa only [Work.FTS.EllipticEst.sliceV] using hA1)
  -- hence `(u')² thEta` is integrable
  have hthInt : Integrable (fun θ => C₁ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [hIoo]
    exact Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul (C₁ ^ 2)
  have hD2Ioo : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hthInt
      (((hd1.continuousOn.pow 2).mul continuousOn_thEta).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθI))]
    have hb : (deriv u θ) ^ 2 ≤ C₁ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC₁ θ hθ) 2
    exact mul_le_mul_of_nonneg_right hb (thEta_nonneg_Iθ hθI)
  have hD2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    show MeasureTheory.Integrable _ (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    rw [← hIoo]
    exact hD2Ioo
  -- `(u')²` and `u'` are integrable on the open interval
  have hD2sq : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hD2Ioo
      ((hd1.continuousOn.pow 2).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
    rw [Real.norm_of_nonneg (sq_nonneg (deriv u θ))]
    calc (deriv u θ) ^ 2 = (deriv u θ) ^ 2 * 1 := by ring
      _ ≤ (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hD1 : MeasureTheory.IntegrableOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono'
      (g := fun θ => (1 / 2) * ((deriv u θ) ^ 2 + 1))
      ((hD2sq.add (integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (C := (1 : ℝ))
        volume_Ioo_lt_top)).const_mul (1 / 2))
      (hd1.continuousOn.aestronglyMeasurable hIooMeas) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    have h2 : |deriv u θ| ≤ (1 / 2) * ((deriv u θ) ^ 2 + 1) := by
      nlinarith [sq_nonneg (|deriv u θ| - 1), sq_abs (deriv u θ)]
    exact h2
  -- `u` is bounded on the open interval
  obtain ⟨C₀, hC₀nn, hC₀⟩ :=
    Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv hpi (φ := u)
      (fun θ hθ => ((((hu 1).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt)) hD1
  -- hence `u² thEta` is integrable
  have hthInt0 : Integrable (fun θ => C₀ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [hIoo]
    exact Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul (C₀ ^ 2)
  have hU2Ioo : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hthInt0
      ((((hu 0).continuousOn.pow 2).mul continuousOn_thEta).aestronglyMeasurable hIooMeas) ?_
    filter_upwards [haeMem] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (thEta_nonneg_Iθ hθI))]
    have hb : (u θ) ^ 2 ≤ C₀ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC₀ θ hθ) 2
    exact mul_le_mul_of_nonneg_right hb (thEta_nonneg_Iθ hθI)
  refine ⟨?_, hD2⟩
  show MeasureTheory.Integrable _ (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [← hIoo]
  exact hU2Ioo

/-! ## Integrability of the slice groups of `f` and of `∂_θ f`

The `j`-th slice group of `f` is `w(z)² · sliceW (4-j) α u` with `u` the `j`-th slice of `f`
(`VopAux.sliceGroup_eq_sliceW`), that of `∂_θ f` is `w(z)² · sliceW (4-j) α (deriv u)`
(`VopAux.sliceGroup_pth_eq_sliceW`).  For `j ≤ 3` the endpoint traces of the slice `u` are
available and the single-slice estimates `VopAux.sliceF_le_sliceV` /
`VopAux.sliceF_deriv_le_sliceV` deliver the integrability of the two `sliceW`'s; for `j = 4`
(where `sliceW 0` is just the `η`-weighted square) the trace-free lemma
`sliceBdd_of_sq_sliceV` above is used instead.  Both need only the per-`z` integrability of the
`ℋ⁴`-integrand of `∂_θ² f` (`VopAux.integrableOn_sliceV_thEta`,
`VopAux.integrableOn_sliceV_LopIter`). -/

/-- Every slice group vanishes identically at `z = 0`, where `w 0 = 0`. -/
theorem sliceGroup_at_zero (α : ℝ) (k j : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.FTS.EllipticEst.sliceGroup α k j F 0 θ = 0 := by
  simp only [Work.FTS.EllipticEst.sliceGroup, Work.Spaces.Wt, Work.Spaces.w]
  simp

/-- **Integrability of the slice groups.**  For `f` of class `C^∞` on the open quadrant whose
`ℋ⁴`-integrand of `∂_θ² f` is integrable on `Iθ` at every `z ∈ Iz`, and whose slices
`θ' ↦ D_z^j f z θ'` have vanishing endpoint traces for `j ≤ 3` and every `z > 0`, the `j`-th
slice group of `f` and of `∂_θ f` is integrable on `Iθ` at every `z ∈ Iz`, for every `j ≤ 4`. -/
theorem sliceGroupIntegrableEasy : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f →
    (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) →
    ∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ)
        Work.Spaces.Iθ := by
  intro α f hα0 hα1 hSO htr hInt z hz j hj
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: both integrands vanish identically
    subst hz0
    constructor
    · refine MeasureTheory.integrableOn_zero.congr ?_
      exact Filter.Eventually.of_forall fun θ => (sliceGroup_at_zero α 4 j f θ).symm
    · refine MeasureTheory.integrableOn_zero.congr ?_
      exact Filter.Eventually.of_forall fun θ =>
        (sliceGroup_at_zero α 4 j (Work.Spaces.pth f) θ).symm
  · have hInt4 := hInt z hz
    set u : ℝ → ℝ := fun θ' => Work.Spaces.DzIter j f z θ' with hu
    have husm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllSol.VopAux.contDiffOn_slice_of_smoothOpen (hSO.DzIter j) hzpos
    have hAj : MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ :=
      Work.FTS.EllSol.VopAux.integrableOn_sliceV_thEta (α := α) (k := 4) (f := f) hSO hzpos hj
        hInt4
    have hBj : ∀ m ∈ Finset.Icc 1 (4 - j), MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro m hm
      have hmj : m + j ≤ 4 := by
        have h2 := (Finset.mem_Icc.mp hm).2
        omega
      exact Work.FTS.EllSol.VopAux.integrableOn_sliceV_LopIter (α := α) (k := 4) (f := f) hSO
        hzpos (Finset.mem_Icc.mp hm).1 hmj hInt4
    rcases le_or_gt j 3 with hj3 | hj3
    · -- `j ≤ 3`: the endpoint traces of the slice are available
      have htrj := htr j hj3 z hzpos
      obtain ⟨h1, h2, -⟩ := RPAe.sliceF_le_sliceV_apply (4 - j) α u hα0 hα1 husm htrj.1 htrj.2
        hAj hBj
      obtain ⟨h1', h2', -⟩ := RPAe.sliceF_deriv_le_sliceV_apply (4 - j) α u hα0 hα1 husm htrj.1
        htrj.2 hAj hBj
      have hWu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW (4 - j) α u θ) Work.Spaces.Iθ :=
        Work.FTS.EllSol.VopAux.integrableOn_sliceW_of (K := 4 - j) h1 h2
      have hWdu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW (4 - j) α (deriv u) θ) Work.Spaces.Iθ :=
        Work.FTS.EllSol.VopAux.integrableOn_sliceW_of (K := 4 - j) h1' h2'
      constructor
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α u θ
          = Work.FTS.EllipticEst.sliceGroup α 4 j f z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j f hzpos (fun n => hSO.forall n) θ hθ]
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWdu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α (deriv u) θ
          = Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW α 4 j f hzpos
          (fun n => hSO.forall n) θ hθ]
    · -- `j = 4`: no trace is available; use the trace-free `η`-weighted bounds
      have hj4 : j = 4 := by omega
      subst hj4
      obtain ⟨hU2, hD2⟩ := sliceBdd_of_sq_sliceV husm hAj
      have hWu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW 0 α u θ) Work.Spaces.Iθ := by
        refine hU2.congr ?_
        exact Filter.Eventually.of_forall fun θ => by simp [Work.FTS.EllSol.VopAux.sliceW]
      have hWdu : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllSol.VopAux.sliceW 0 α (deriv u) θ) Work.Spaces.Iθ := by
        refine hD2.congr ?_
        exact Filter.Eventually.of_forall fun θ => by simp [Work.FTS.EllSol.VopAux.sliceW]
      constructor
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW 0 α u θ
          = Work.FTS.EllipticEst.sliceGroup α 4 4 f z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 4 f hzpos (fun n => hSO.forall n)
          θ hθ]
      · refine MeasureTheory.Integrable.congr
          (MeasureTheory.Integrable.const_mul hWdu ((Work.Spaces.w z) ^ 2)) ?_
        refine Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo ?_
        intro θ hθ
        show (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW 0 α (deriv u) θ
          = Work.FTS.EllipticEst.sliceGroup α 4 4 (Work.Spaces.pth f) z θ
        rw [Work.FTS.EllSol.VopAux.sliceGroup_pth_eq_sliceW α 4 4 f hzpos
          (fun n => hSO.forall n) θ hθ]

end Work.FTS.EllSol.RPAe
end
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.TraceIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Per-`z` comparison of the `ℋ^k`-integrands for `f`** (the `∂_θ²`-case): the angular
integral of the `ℋ^k`-integrand of `f` is bounded by a constant times that of `∂_θ²f`, and the
integrand of `f` is itself integrable.  The constant is uniform in `α ∈ (0,1]` and in `f`; it
depends only on the level `k`. -/
theorem HkIntegrand_integral_le_pth2_trace (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
  classical
  have hcf := fun K => Classical.choose_spec (sliceF_le_sliceV K)
  let C : ℝ := (∑ K ∈ Finset.range (k + 1),
    Classical.choose (sliceF_le_sliceV K)) + 1
  have hCpos : 0 < C := by
    have h1 : 0 < ∑ K ∈ Finset.range (k + 1), Classical.choose (sliceF_le_sliceV K) :=
      Finset.sum_pos (fun K _ => (hcf K).1)
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    simp only [C]; linarith
  have hCle : ∀ K ≤ k, Classical.choose (sliceF_le_sliceV K) ≤ C := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : Classical.choose (sliceF_le_sliceV K)
        ≤ ∑ K' ∈ Finset.range (k + 1), Classical.choose (sliceF_le_sliceV K') :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcf K').1) hmem
    simp only [C]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α f hα0 hα1 hf htrace hInt z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: both integrands vanish
    subst hz0
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k f θ]
      exact integrableOn_zero
    · rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f 0 θ) = 0 from by
        rw [show (fun θ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ : ℝ => (0 : ℝ) from
          funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k f θ]
        simp]
      exact mul_nonneg (le_of_lt hCpos) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pthIter 2 f) 0 θ))
  · -- `z > 0`
    have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
    have hIntV : ∀ j ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceV_thEta hf hzpos hj (hInt z hz)
    have hIntL : ∀ j ≤ k, ∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro j hj m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmj : m + j ≤ k := by
        have h2 := (Finset.mem_Icc.mp hm).2; omega
      exact integrableOn_sliceV_LopIter hf hzpos hm1 hmj (hInt z hz)
    -- the single-slice estimate for every radial level `j ≤ k`
    have hslice : ∀ j ≤ k,
        MeasureTheory.IntegrableOn (fun θ =>
          (fun θ' => Work.Spaces.DzIter j f z θ') θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            Work.Spaces.Iθ ∧
        (∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
          (Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) ∧
        sliceF (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ')
          ≤ Classical.choose (sliceF_le_sliceV (k - j))
            * sliceF (k - j) α
                (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
      fun j hj => (hcf (k - j)).2 α (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1
        (contDiffOn_slice_of_smoothOpen (hf.DzIter j) hzpos)
        (htrace j hj z hzpos).1 (htrace j hj z hzpos).2 (hIntV j hj) (hIntL j hj)
    -- integrability of the slice groups of `f`
    have hgrpF : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j f z θ) Work.Spaces.Iθ := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, -⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      refine (hintW.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
          (Work.Spaces.w z) ^ 2
            * sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
        (v := fun θ => Work.FTS.EllipticEst.sliceGroup α k j f z θ)
        (fun θ hθ => (sliceGroup_eq_sliceW α k j f hzpos hf.forall θ hθ).symm)] with θ hθ
      exact hθ
    -- integrability of the slice groups of `∂_θ² f`
    have hgrp2 : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
          Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceGroup_of_HkIntegrand hpth2 hzpos
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (hInt z hz)
    have hdecomp : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        = ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ => Work.FTS.EllipticEst.sliceGroup α k j f z θ) hgrpF]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k f z θ)
    have hdecomp2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) hgrp2]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pthIter 2 f) z θ)
    have hgroup_bound : ∀ j ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, hbnd⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      have hintW2 : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j)
        (hIntV j hjle) (hIntL j hjle)
      rw [integral_sliceGroup_eq_sliceF α k j f hzpos hf hintW,
        integral_sliceGroup_pthIter2_eq_sliceF α k j f hzpos hf hintW2]
      have hFnn : 0 ≤ sliceF (k - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
        sliceF_nonneg _ _ _
      calc (Work.Spaces.w z) ^ 2 * sliceF (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ')
          ≤ (Work.Spaces.w z) ^ 2 * (Classical.choose (sliceF_le_sliceV (k - j))
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
            mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
        _ = (Classical.choose (sliceF_le_sliceV (k - j)) * (Work.Spaces.w z) ^ 2)
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            ring
        _ ≤ (C * (Work.Spaces.w z) ^ 2) * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            refine mul_le_mul_of_nonneg_right ?_ hFnn
            exact mul_le_mul_of_nonneg_right (hCle (k - j) (Nat.sub_le k j)) (sq_nonneg _)
        _ = C * ((Work.Spaces.w z) ^ 2 * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
            ring
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          = fun θ => ∑ j ∈ Finset.range (k + 1),
              Work.FTS.EllipticEst.sliceGroup α k j f z θ from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k f z θ]
      exact MeasureTheory.integrable_finsetSum _ hgrpF
    · calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          = ∑ j ∈ Finset.range (k + 1),
              ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ :=
            hdecomp
        _ ≤ ∑ j ∈ Finset.range (k + 1), C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) :=
            Finset.sum_le_sum hgroup_bound
        _ = C * ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ :=
            (Finset.mul_sum ..).symm
        _ = C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
            rw [hdecomp2]

/-- **Per-`z` comparison of the `ℋ^k`-integrands for `∂_θ f`** (the `∂_θ`-case). -/
theorem HkIntegrand_integral_le_pth2_pth_trace (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
  classical
  have hcd := fun K => Classical.choose_spec (sliceF_deriv_le_sliceV K)
  let C : ℝ := (∑ K ∈ Finset.range (k + 1),
    Classical.choose (sliceF_deriv_le_sliceV K)) + 1
  have hCpos : 0 < C := by
    have h1 : 0 < ∑ K ∈ Finset.range (k + 1), Classical.choose (sliceF_deriv_le_sliceV K) :=
      Finset.sum_pos (fun K _ => (hcd K).1)
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    simp only [C]; linarith
  have hCle : ∀ K ≤ k, Classical.choose (sliceF_deriv_le_sliceV K) ≤ C := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : Classical.choose (sliceF_deriv_le_sliceV K)
        ≤ ∑ K' ∈ Finset.range (k + 1), Classical.choose (sliceF_deriv_le_sliceV K') :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcd K').1) hmem
    simp only [C]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α f hα0 hα1 hf htrace hInt z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ)
          = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k
          (Work.Spaces.pth f) θ]
      exact integrableOn_zero
    · rw [show (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ) = 0 from by
        rw [show (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ)
            = fun _ : ℝ => (0 : ℝ) from
          funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k
            (Work.Spaces.pth f) θ]
        simp]
      exact mul_nonneg (le_of_lt hCpos) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pthIter 2 f) 0 θ))
  · have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
    have hIntV : ∀ j ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceV_thEta hf hzpos hj (hInt z hz)
    have hIntL : ∀ j ≤ k, ∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro j hj m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmj : m + j ≤ k := by
        have h2 := (Finset.mem_Icc.mp hm).2; omega
      exact integrableOn_sliceV_LopIter hf hzpos hm1 hmj (hInt z hz)
    have hslice : ∀ j ≤ k,
        MeasureTheory.IntegrableOn (fun θ =>
          (deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
        (∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
          (Work.FTS.EllipticEst.LopIter i (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) ∧
        sliceF (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
          ≤ Classical.choose (sliceF_deriv_le_sliceV (k - j))
            * sliceF (k - j) α
                (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
      fun j hj => (hcd (k - j)).2 α (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1
        (contDiffOn_slice_of_smoothOpen (hf.DzIter j) hzpos)
        (htrace j hj z hzpos).1 (htrace j hj z hzpos).2 (hIntV j hj) (hIntL j hj)
    have hgrpP : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ) Work.Spaces.Iθ := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, -⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      refine (hintW.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
          (Work.Spaces.w z) ^ 2
            * sliceW (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
        (v := fun θ => Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
        (fun θ hθ => (sliceGroup_pth_eq_sliceW α k j f hzpos hf.forall θ hθ).symm)]
        with θ hθ
      exact hθ
    have hgrp2 : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
          Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceGroup_of_HkIntegrand hpth2 hzpos
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (hInt z hz)
    have hdecomp : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
        = ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ) hgrpP]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pth f) z θ)
    have hdecomp2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) hgrp2]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pthIter 2 f) z θ)
    have hidentP : ∀ j ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
          = (Work.Spaces.w z) ^ 2 * sliceF (k - j) α
              (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) := by
      intro j _
      rw [sliceF, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
        (v := fun θ => (Work.Spaces.w z) ^ 2 * sliceW (k - j) α
          (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
        (fun θ hθ => sliceGroup_pth_eq_sliceW α k j f hzpos hf.forall θ hθ)] with θ hθ
      exact hθ
    have hgroup_bound : ∀ j ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, hbnd⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      have hintW2 : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j)
        (hIntV j hjle) (hIntL j hjle)
      rw [hidentP j hj,
        integral_sliceGroup_pthIter2_eq_sliceF α k j f hzpos hf hintW2]
      have hFnn : 0 ≤ sliceF (k - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
        sliceF_nonneg _ _ _
      calc (Work.Spaces.w z) ^ 2
              * sliceF (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
          ≤ (Work.Spaces.w z) ^ 2 * (Classical.choose (sliceF_deriv_le_sliceV (k - j))
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
            mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
        _ = (Classical.choose (sliceF_deriv_le_sliceV (k - j)) * (Work.Spaces.w z) ^ 2)
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            ring
        _ ≤ (C * (Work.Spaces.w z) ^ 2) * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            refine mul_le_mul_of_nonneg_right ?_ hFnn
            exact mul_le_mul_of_nonneg_right (hCle (k - j) (Nat.sub_le k j)) (sq_nonneg _)
        _ = C * ((Work.Spaces.w z) ^ 2 * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
            ring
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          = fun θ => ∑ j ∈ Finset.range (k + 1),
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k
          (Work.Spaces.pth f) z θ]
      exact MeasureTheory.integrable_finsetSum _ hgrpP
    · calc (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ := hdecomp
        _ ≤ ∑ j ∈ Finset.range (k + 1), C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) :=
            Finset.sum_le_sum hgroup_bound
        _ = C * ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ :=
            (Finset.mul_sum ..).symm
        _ = C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
            rw [hdecomp2]

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.PsiSlices

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## §4 The angular moments of `∂_zΨ` and `∂_z²Ψ` -/

/-- From the box integrability of `g·sinθcos²θ`, the moment `F_*(g)` is interval integrable. -/
theorem intervalIntegrable_Fstar_of_box {g : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hbox : Integrable (Function.uncurry (fun r θ : ℝ => g r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ))) :
    IntervalIntegrable (Work.Elliptic.Fstar g) volume a b := by
  have hint : IntegrableOn (Work.Elliptic.Fstar g) (Set.Ioc a b) := by
    have h := hbox.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun r => ?_)
    show (∫ θ, Function.uncurry (fun r θ : ℝ => g r θ * Work.Elliptic.sinCos2 θ) (r, θ)
        ∂(volume.restrict Work.Spaces.Iθ)) = Work.Elliptic.Fstar g r
    rw [Work.Elliptic.Fstar]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => rfl)
  have hIcc : IntegrableOn (Work.Elliptic.Fstar g) (Set.Icc a b) := by
    change Integrable (Work.Elliptic.Fstar g) (volume.restrict (Set.Icc a b))
    rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))]
    exact hint
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
  exact hIcc

/-- `F_*(∂_zΨ) = 0` a.e., from `F_* Ψ = 0` a.e. -/
theorem Fstar_pz_ae_zero {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (h0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0 :=
  ae_eq_zero_of_moment_chain (W := Work.Elliptic.Fstar Ψ)
    (V := Work.Elliptic.Fstar (Work.Spaces.pz Ψ))
    (fun s t hs hst => Fstar_sub_pz hΨ hB hs hst) h0
    (fun a b ha hab => intervalIntegrable_Fstar_of_box hab (box_pz hΨ hB ha hab.le))

/-- `F_*(∂_z²Ψ) = 0` a.e., from `F_*(∂_zΨ) = 0` a.e. -/
theorem Fstar_pzIter2_ae_zero {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (h0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z = 0 :=
  ae_eq_zero_of_moment_chain (W := Work.Elliptic.Fstar (Work.Spaces.pz Ψ))
    (V := Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ))
    (fun s t hs hst => Fstar_sub_pzIter2 hΨ hB hs hst) h0
    (fun a b ha hab => intervalIntegrable_Fstar_of_box hab (box_pzIter2 hΨ hB ha hab.le))

/-! ## §5 The shift from `∂_z^j` to `D_z^j` -/

/-- `F_*(D_z f)(z) = z·F_*(∂_z f)(z)`. -/
theorem Fstar_Dz_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Spaces.Dz f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.Dz f z θ * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => z * (Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-- The product rule for `D_z²`: `D_z²f = z ∂_zf + z²∂_z²f` on the open quadrant. -/
theorem DzIter_two_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 f z θ
      = z * Work.Spaces.pz f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ := by
  have hfd : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz f z' θ)
      (Work.Spaces.pz f z θ + z * Work.Spaces.pzIter 2 f z θ) z := by
    have h1 : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz f z' θ)
        (Work.Spaces.pzIter 2 f z θ) z := by
      have h := hf.hasDerivAt_slice_pzIter 1 hθ hz
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
    have h := h1.mul h2
    convert h using 1
    ring
  have hderiv : Work.Spaces.pz (Work.Spaces.Dz f) z θ
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z := rfl
  show z * Work.Spaces.pz (Work.Spaces.Dz f) z θ
    = z * Work.Spaces.pz f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ
  rw [hderiv, hfd.deriv]
  ring

/-- The moment of `D_z²` in terms of the moments of `∂_z` and `∂_z²`. -/
theorem Fstar_DzIter_two_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ}
    (hz : 0 < z)
    (hsl1 : IntegrableOn (fun θ : ℝ => Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hsl2 : IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 f z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 2 f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z
        + z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 f) z := by
  have hae : (fun θ : ℝ => Work.Spaces.DzIter 2 f z θ * Work.Elliptic.sinCos2 θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => z * (Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ)
        + z ^ 2 * (Work.Spaces.pzIter 2 f z θ * Work.Elliptic.sinCos2 θ)) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => by
      show Work.Spaces.DzIter 2 f z θ * Work.Elliptic.sinCos2 θ
        = z * (Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ)
          + z ^ 2 * (Work.Spaces.pzIter 2 f z θ * Work.Elliptic.sinCos2 θ)
      rw [DzIter_two_eq hf hz hθ]; ring)] with θ hθ
    exact hθ
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar,
    MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add (hsl1.const_mul z) (hsl2.const_mul (z ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- `θ ↦ (∂_z²Ψ)(u,θ)·sinθcos²θ` is integrable on `Iθ` for `u > 0`. -/
theorem slice_pzIter2_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  have h1 := slice_abs_integrableOn hΨ hB 2 (by norm_num) hu
  have h2 : IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.Dz Ψ u θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (slice_abs_integrableOn hΨ hB 1 (by norm_num) hu).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        show |Work.Spaces.DzIter 1 Ψ u θ| * Work.Elliptic.sinCos2 θ
          = |Work.Spaces.Dz Ψ u θ| * Work.Elliptic.sinCos2 θ
        rfl))
  have h3 : IntegrableOn (fun θ : ℝ => (|Work.Spaces.DzIter 2 Ψ u θ|
      + |Work.Spaces.Dz Ψ u θ|) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (h1.add h2).congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => by
        show |Work.Spaces.DzIter 2 Ψ u θ| * Work.Elliptic.sinCos2 θ
            + |Work.Spaces.Dz Ψ u θ| * Work.Elliptic.sinCos2 θ
          = (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ
        ring))
  have hmaj : IntegrableOn (fun θ : ℝ => (|Work.Spaces.DzIter 2 Ψ u θ|
      + |Work.Spaces.Dz Ψ u θ|) * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹) Work.Spaces.Iθ :=
    (h3.const_mul (u ^ 2)⁻¹).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        show (u ^ 2)⁻¹ * ((|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ)
          = (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹
        ring))
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((hΨ.aesm_slice_pzIter 2 hu).mul continuous_sinCos2.aestronglyMeasurable)
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hθ)] with θ hθ hθmem
    have hid := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hu hθmem
    have hdiv : Work.Spaces.pzIter 2 Ψ u θ
        = (Work.Spaces.DzIter 2 Ψ u θ - Work.Spaces.Dz Ψ u θ) / u ^ 2 := by
      rw [← hid]
      field_simp
    show ‖Work.Spaces.pzIter 2 Ψ u θ * Work.Elliptic.sinCos2 θ‖
      ≤ (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
        * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ), hdiv, abs_div,
      abs_of_pos hu2]
    calc |Work.Spaces.DzIter 2 Ψ u θ - Work.Spaces.Dz Ψ u θ| / u ^ 2
          * Work.Elliptic.sinCos2 θ
        ≤ (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|) / u ^ 2
            * Work.Elliptic.sinCos2 θ :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (abs_sub _ _) (le_of_lt hu2))
            (sinCos2_nonneg hθ)
      _ = (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹ := by ring

/-! ## §6 The a.e. moments of the `Ψ`-slices -/

/-- **The angular moment of `D_z^jΨ` vanishes a.e. for `j ≤ 2`.** -/
theorem Fstar_DzIter_Psi_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hPsi0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthPsi
  have hA := Fstar_pz_ae_zero hΨ hB hPsi0
  have hA2 := Fstar_pzIter2_ae_zero hΨ hB hA
  intro j hj
  interval_cases j
  · exact hPsi0
  · filter_upwards [hA] with z hz
    show Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0
    rw [show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl, Fstar_Dz_eq, hz, mul_zero]
  · filter_upwards [hA, hA2, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hz2 hzpos
    show Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0
    rw [Fstar_DzIter_two_eq hΨ hzpos (slice_abs_pz_integrableOn hΨ hB hzpos)
      (slice_pzIter2_integrableOn hΨ hB hzpos), hz, hz2]
    ring

/-! ## §7 The a.e. moments of the `F`-slices -/

/-- **The angular moment of `D_z^jF` vanishes a.e. for `j ≤ 2`.** -/
theorem Fstar_DzIter_F_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  have hmem : Work.Spaces.HkMem α 2 F := h.memF
  -- the interval integrability of the divided moments
  have hInt : ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        volume a b := by
    intro j hj a b ha hab
    have h1 := Work.FTS.EllipticEst.integrableOn_Bmom_div α 2 hF hmem j hj a b ha hab
    have h2 : IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        (Set.Icc a b) :=
      h1.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => by
        show Work.FTS.EllipticEst.Bmom F j r / r
          = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r
        rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact h2
  -- `j = 0`
  have h0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar F z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthF
  -- `j = 1`
  have h1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
    have hraw := ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar F)
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF hmem
        0 (by norm_num) hs hst)
      h0 (hInt 1 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  -- `j = 2`
  have h2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
    have hraw := ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F))
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF hmem
        1 (by norm_num) hs hst)
      h1 (hInt 2 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  intro j hj
  interval_cases j
  · simpa using h0
  · exact h1
  · exact h2

end Work.FTS.EllipticEst.H2W.PsiSlices
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.PerMode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

set_option maxHeartbeats 3200000
/-! ## The operator applied to a smooth function is continuous -/

/-- `bslOp α ψ` is continuous on the open quadrant for a smooth `ψ`. -/
theorem continuousOn_bslOp {α : ℝ} {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pzIter 2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pz).continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.EllipticEst.ModalSolution.continuousOn_Lzero hψ
  have hz : ContinuousOn (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := continuousOn_fst
  have h4 : ContinuousOn (fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2)) Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul (hz.pow 2)).neg
  have h5 : ContinuousOn (fun p : ℝ × ℝ => α * (5 + α) * p.1) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const.mul hz
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      -(α ^ 2 * p.1 ^ 2) * Work.Spaces.pzIter 2 ψ p.1 p.2
        - (α * (5 + α) * p.1) * Work.Spaces.pz ψ p.1 p.2
        + Work.Elliptic.Lzero ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((h4.mul h1).sub (h5.mul h2)).add h3
  simpa only [Work.Elliptic.bslOp_apply] using hmain

/-! ## The per-mode identity on the quadrant -/

/-- **The per-mode weak identity.** -/
theorem perModeQ0 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0,
          (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
            * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  obtain ⟨a, b, c, d, ha, hab, hc0, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 :=
    fun p hp => Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hKmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- ## integrability on the box
  have hAcont : ContinuousOn (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Icc a b) := by
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact (radGreenContinuousOn hα hα1 m hc2 hcm).mono
      (fun z hz => lt_of_lt_of_le ha hz.1)
  have hem : Continuous (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous
  have hzq : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 ^ ((5 - α) / α) * Real.cos p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.rpow_const (fun p hp =>
      Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
      (Real.continuous_cos.comp_continuousOn continuousOn_snd)
  have hbsl : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α φ p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) := (continuousOn_bslOp hφsm).mono hKsub
  have hLint : IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((((hAcont.comp continuousOn_fst (fun p hp => hp.1)).mul
      (hem.comp_continuousOn continuousOn_snd)).mul hbsl).mul hzq).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2
      * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((hem.comp_continuousOn continuousOn_snd).mul (hφsm.continuousOn.mono hKsub)).mul hzq
  have hRint : IntegrableOn (fun p : ℝ × ℝ =>
      (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    have hbase := Work.FTS.H2.ModalSol.Aux.integrableOn_mul_of_sq_integrable hc2 hcm ha hab.le
      hc0 hcd.le hg
    refine hbase.congr_fun (fun p _ => ?_) hKmeas
    ring
  -- ## reduction of both sides to the box
  have hLred : (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
        (Work.FTS.PhiStar.Series.acoeff α m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      rw [bslOp_eq_zero_off_box hbox hp.2]
      ring)
  have hRred : (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
        (Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) :=
    setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      have hφ0 : φ p.1 p.2 = 0 := by
        by_cases h1 : p.1 ∈ Set.Ioo a b
        · exact test_vanishes_off_theta hbox
            (fun h2 => hp.2 ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩⟩)
        · exact test_vanishes_off_z hbox h1
      rw [hφ0]
      ring)
  rw [hLred, hRred, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.setIntegral_prod _ hLint, MeasureTheory.setIntegral_prod _ hRint]
  exact perMode_box α hα hα1 m hm hc2 hcm hφ hφc hφs ha hab hc0 hcd hd hbox

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBP_subSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-- **Integration by parts for the sub-slot operators.**  For `f` smooth on the open quadrant and `φ` a test function on `Q0`, the formal transpose `subSlotStar r j i` moves `subSlot r j i = D_z^j D_θ^i ∘ slot_r` off `f` and onto `φ`, and the transposed test function is again a test function.  (This is the composition of `IBP_mixed` with the elementary identity `∫ (z² ∂_z² f) φ = ∫ f (∂_z² (z² φ))` for the first slot, two-dimensional integration by parts for `∂_θ²` for the second, and their combination with `D_z = z ∂_z` for the third.) -/
theorem IBP_subSlot (r j i : ℕ) {f φ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hφ : TestQ0 φ) :
    TestQ0 (subSlotStar r j i φ) ∧
      (∫ p in Work.FTS.EllipticEst.Q0,
          subSlot r j i f p.1 p.2 * φ p.1 p.2
        = ∫ p in Work.FTS.EllipticEst.Q0,
          f p.1 p.2 * subSlotStar r j i φ p.1 p.2) := by
  have hmix : TestQ0 (mixedStar j i φ) := testQ0_mixedStar hφ j i
  have hstar : TestQ0 (subSlotStar r j i φ) := by
    rcases r with _ | _ | r
    · exact testQ0_slot1Star hmix
    · exact testQ0_slot2Star hmix
    · exact testQ0_slot3Star hmix
  refine ⟨hstar, ?_⟩
  have hL : ∫ p in Q0, subSlot r j i f p.1 p.2 * φ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.mixed j i (slot r f) p.1 p.2 * φ p.1 p.2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
    have hφ0 : φ p.1 p.2 = 0 := by
      by_contra hne
      exact hp (hφ.tsupp (subset_closure (Function.mem_support.mpr hne)))
    rw [hφ0, mul_zero]
  have hR : ∫ p in Q0, f p.1 p.2 * subSlotStar r j i φ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * subSlotStar r j i φ p.1 p.2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
    have h0 : subSlotStar r j i φ p.1 p.2 = 0 := by
      by_contra hne
      exact hp (hstar.tsupp (subset_closure (Function.mem_support.mpr hne)))
    rw [h0, mul_zero]
  rw [hL, hR]
  exact integral_mixed_subSlot r j i hf hφ

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem psiTrunc_tendsto_psiSeries {α : ℝ} {F : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (horth : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
      (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)) := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  obtain ⟨Ce, hCe, hCeb⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have hcm : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0) :=
    fun m => Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  have hcnn : ∀ m : ℕ, 0 ≤ ∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2 :=
    fun m => MeasureTheory.integral_nonneg (fun t => sq_nonneg _)
  -- `B m = ‖cmode m F‖_{L²(0,∞)}`, `D m = √m · B m`
  set B : ℕ → ℝ := fun m => Real.sqrt
    (∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2) with hBdef
  set D : ℕ → ℝ := fun m => Real.sqrt (m : ℝ) * B m with hDdef
  have hBnn : ∀ m : ℕ, 0 ≤ B m := fun m => Real.sqrt_nonneg _
  have hBsq : ∀ m : ℕ, B m ^ 2 = ∫ t in Set.Ioi 0,
      Work.FTS.PhiStar.Series.cmode m F t ^ 2 := fun m => Real.sq_sqrt (hcnn m)
  have hDnn : ∀ m : ℕ, 0 ≤ D m := fun m =>
    mul_nonneg (Real.sqrt_nonneg _) (hBnn m)
  have hDsq : ∀ m : ℕ, D m ^ 2 = (m : ℝ) *
      ∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2 := by
    intro m
    rw [hDdef, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), hBsq m]
  -- ## Bessel: `∑ D m² ≤ ∫_{Q0} F²`
  have hDsum : Summable (fun m : ℕ => D m ^ 2) := by
    have hle : ∀ j : ℕ, (j : ℝ) ≤ Work.EllipticEst.ModalSolution.eNorm j := by
      intro j
      rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (j : ℝ) + 5)]
      nlinarith [hj]
    have hstep : ∀ j : ℕ, (j : ℝ) * ∫ t in Set.Ioi 0,
          Work.FTS.PhiStar.Series.cmode j F t ^ 2
        ≤ Work.EllipticEst.ModalSolution.eNorm j * ∫ t in Set.Ioi 0,
          Work.FTS.PhiStar.Series.cmode j F t ^ 2 :=
      fun j => mul_le_mul_of_nonneg_right (hle j) (hcnn j)
    have hbd : ∀ N : ℕ, ∑ j ∈ Finset.range N, (j : ℝ) * ∫ t in Set.Ioi 0,
        Work.FTS.PhiStar.Series.cmode j F t ^ 2
        ≤ ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2 := by
      intro N
      refine le_trans (Finset.sum_le_sum (fun j _ => hstep j)) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (Nat.le_succ N))
        (fun j _ _ => mul_nonneg (Work.EllipticEst.ModalSolution.eNorm_pos j).le (hcnn j)))
        (Work.FTS.H2.ModalSolR.coeffL2_sum_le hsm hL2 N)
    have hsum := summable_of_sum_range_le
      (f := fun j : ℕ => (j : ℝ) * ∫ t in Set.Ioi 0,
        Work.FTS.PhiStar.Series.cmode j F t ^ 2)
      (fun j => mul_nonneg (Nat.cast_nonneg j) (hcnn j)) hbd
    refine hsum.congr (fun m => ?_)
    rw [hDsq m]
  -- ## the summable majorant `D m / (m+1)`
  have hgeo : Summable (fun m : ℕ => D m / ((m : ℝ) + 1)) := by
    have hone : Summable (fun m : ℕ => (1 / ((m : ℝ) + 1)) ^ 2) := by
      have h2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h3 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
        have h4 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h2
        simpa only [Nat.cast_add, Nat.cast_one] using h4
      refine h3.congr (fun m => ?_)
      rw [div_pow, one_pow]
    have h2 : Summable (fun m : ℕ => (D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) / 2) :=
      (hDsum.add hone).div_const 2
    refine Summable.of_nonneg_of_le (fun m => div_nonneg (hDnn m) (by positivity))
      (fun m => ?_) h2
    have hmain : 2 * (D m / ((m : ℝ) + 1))
        ≤ D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2 := by
      have h := two_mul_le_add_sq (D m) (1 / ((m : ℝ) + 1))
      have hrw : 2 * (D m / ((m : ℝ) + 1)) = 2 * D m * (1 / ((m : ℝ) + 1)) := by ring
      rw [hrw]
      exact h
    have hhalf : (D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) / 2
        = (1 / 2) * (D m ^ 2 + (1 / ((m : ℝ) + 1)) ^ 2) := by ring
    rw [hhalf]
    linarith [hmain]
  -- ## the pointwise bound on the mode terms, `m ≥ 1`
  have hterm : ∀ m : ℕ, 1 ≤ m →
      ‖Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ (Ce * z ^ (-(1 / 2) : ℝ) / α) * (D m / ((m : ℝ) + 1)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hrm0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
    have hsqm : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm0.le
    have hrad := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm (hcm m) hz
    have hE := hCeb m θ hIθ
    have hden : 0 < α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) :=
      mul_pos (mul_pos hα (by linarith)) hrm0
    have hBm0 : 0 ≤ B m * z ^ (-(1 / 2) : ℝ) :=
      mul_nonneg (hBnn m) (Real.rpow_nonneg hz.le (-(1 / 2)))
    have hcoef : 0 ≤ B m * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) :=
      div_nonneg hBm0 hden.le
    have hcore : |Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.Series.cmode m F) z|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤
        (B m * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)))
          * (Ce * ((m : ℝ) + 1)) :=
      mul_le_mul hrad hE (abs_nonneg _) hcoef
    have hkey : ((m : ℝ) + 1) ^ 2 ≤ (m : ℝ) * (4 * (m : ℝ) + 5) := by nlinarith
    have hfac : (B m * z ^ (-(1 / 2) : ℝ) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)))
          * (Ce * ((m : ℝ) + 1))
        = (Ce * z ^ (-(1 / 2) : ℝ) / α)
          * (B m * ((m : ℝ) + 1) / ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) := by
      have h1 : Real.sqrt (m : ℝ) ≠ 0 := hrm0.ne'
      have h2 : α ≠ 0 := hα.ne'
      have h3 : (4 * (m : ℝ) + 5) ≠ 0 := by linarith
      field_simp
      try ring
    have hDrel : D m = Real.sqrt (m : ℝ) * B m := by rw [hDdef]
    have htail : B m * ((m : ℝ) + 1) / ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))
        ≤ D m / ((m : ℝ) + 1) := by
      have hle : B m * ((m : ℝ) + 1) * ((m : ℝ) + 1)
          ≤ D m * ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) := by
        rw [hDrel]
        calc B m * ((m : ℝ) + 1) * ((m : ℝ) + 1) = B m * (((m : ℝ) + 1) ^ 2) := by ring
          _ ≤ B m * ((m : ℝ) * (4 * (m : ℝ) + 5)) :=
              mul_le_mul_of_nonneg_left hkey (hBnn m)
          _ = B m * ((4 * (m : ℝ) + 5) * (m : ℝ)) := by ring
          _ = B m * ((4 * (m : ℝ) + 5) * (Real.sqrt (m : ℝ)) ^ 2) := by rw [hsqm]
          _ = (Real.sqrt (m : ℝ) * B m) * ((4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) := by ring
      have hb : 0 < (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) :=
        mul_pos (by linarith) hrm0
      have hd : 0 < (m : ℝ) + 1 := by linarith
      rw [div_le_div_iff₀ hb hd]
      exact hle
    have hKnn : 0 ≤ Ce * z ^ (-(1 / 2) : ℝ) / α :=
      div_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg hz.le (-(1 / 2)))) hα.le
    rw [Real.norm_eq_abs, abs_mul]
    change |Work.FTS.PhiStar.Radial.radGreen α m
        (Work.FTS.PhiStar.Series.cmode m F) z|
      * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ (Ce * z ^ (-(1 / 2) : ℝ) / α) * (D m / ((m : ℝ) + 1))
    refine le_trans hcore ?_
    rw [hfac]
    exact mul_le_mul_of_nonneg_left htail hKnn
  -- ## summability of the shifted mode family, hence of the family itself
  have hKs : Summable (fun n : ℕ => (Ce * z ^ (-(1 / 2) : ℝ) / α)
      * (D (n + 1) / (((n + 1 : ℕ) : ℝ) + 1))) := by
    have hbase : Summable (fun m : ℕ => (Ce * z ^ (-(1 / 2) : ℝ) / α)
        * (D m / ((m : ℝ) + 1))) := hgeo.mul_left _
    exact (summable_nat_add_iff
      (f := fun m : ℕ => (Ce * z ^ (-(1 / 2) : ℝ) / α) * (D m / ((m : ℝ) + 1))) 1).mpr hbase
  have hshift : Summable (fun n : ℕ => Work.FTS.PhiStar.Series.acoeff α (n + 1) F z
      * Work.FTS.PhiStar.Gegenbauer.eFam (n + 1) θ) :=
    Summable.of_norm_bounded hKs (fun n => hterm (n + 1) (by omega))
  have hfam : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m F z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := (summable_nat_add_iff 1).mp hshift
  -- ## concluding
  show Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    Filter.atTop (nhds (∑' m : ℕ, Work.FTS.PhiStar.Series.acoeff α m F z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ))
  have hfun : (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = ((fun n : ℕ => ∑ m ∈ Finset.range n,
          Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        ∘ fun N : ℕ => N + 1) := by
    funext N
    rfl
  rw [hfun]
  exact hfam.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

end Work.FTS.PhiStar.Honesty
end
end
