import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.mixedSupSix
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.H2.T1Q.SlotOpen
-- ===== merged: Submission.Work.FTS.OpenPkg.fkH_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

theorem fkH_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
  -- the two universal constants: `∫_θ K(θ)²` and `∫_θ sin(2θ)^{-η}`
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (5 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (5 * AK * Cθ)
    linarith
  intro α hαpos hα1 g hg _
  obtain ⟨hsm, hmem⟩ := hg
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang g 0 z with hudef
  -- ## the a.e. identity `D_z^i (FK g) = Qang g i` for `i ≤ 4`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang g i z := by
    filter_upwards [Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hsm hmem,
      MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 4 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 5))]
  -- ## the per-slot integrability and bound
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem hi).1.congr
      (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 4 g := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem hi).2
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 5 * (AK * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int]
    calc ∑ i ∈ Finset.range 5, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (AK * Work.Spaces.HkSq α 4 g) :=
          Finset.sum_le_sum fun i hi => hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (AK * Work.Spaces.HkSq α 4 g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁴`-energy and the norm bound
  have hHkSq : Work.Spaces.HkSq α 4 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 4 (fun z θ => u z) ≤ (5 * AK * Cθ) * Work.Spaces.HkSq α 4 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => u z)
      ≤ Real.sqrt (5 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
    have h5 : 0 ≤ 5 * AK * Cθ := by nlinarith
    calc Work.FTS.Nonlin.Xn α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((5 * AK * Cθ) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (5 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
          rw [Real.sqrt_mul h5]
          rfl
  -- ## membership in `ℋ⁴`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 4 (fun z θ => u z) := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## `FK g` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.classC_sup_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.SupPort.classC_sup_le`

The interior `ℋ⁴ → L^∞` bound on the class `C` of profiles (`ClassC`), i.e. the port of
Elgindi's Corollary `SecondDerivativesBounded` (`Work.FTS.H2.mixed_supAbsO_le`, constant `10`)

  `|D_z^b D_θ^a f(z,θ)| ≤ 10/√(γ-1) · |f|_{ℋ⁴}`   (the `(b,a) = (0,0)` instance here),

from the interior class `RegQ` (`SmoothQuad` = `C^∞` on `z > -1`) to the open class
`ClassC` (whose regularity field is `SmoothOpen` = `C^∞` on `z > 0` only).  The original proof
never uses smoothness for `z ≤ 0`; it is re-run with `SmoothOpen`, the open-quadrant box
`Q0 = (0,∞) × (0,π/2)` replacing `quadU = (-1,∞) × (0,π/2)`.  The three ingredients that
genuinely change are the open-quadrant angular Hardy inequality (`HardyThetaOpen`), the
`θ`-first form of a single `ℋ⁴`-slot (`slotM_open`) and the integrability of the angular Hardy
integrand (`integrableOn_pth_mixed_sq_sin`); the radial Hardy inequality
(`Work.FTS.H2.hardyZ_open`) and the boundary-limit lemmas of `BdryTraces` are already available
in the open form.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.SupPort

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular Hardy inequality

The open-quadrant angular Hardy inequality is supplied by the sibling module
`Submission/Work/FTS/StrongEps.SupPort.HardyThetaOpen` (`SmoothOpen` in place of `SmoothQuad`,
the boundary value at `θ = 0` given by the one-sided limit).  It is the only ingredient of the
port that is not a verbatim re-run of the `SmoothQuad` proof. -/

/-- **`D_θ` of a mixed derivative is the next mixed derivative, on the open quadrant.**
This is `Work.FTS.H2.Dth_mixed_quad` with the open-quadrant hypothesis `SmoothOpen f`
(instead of `SmoothQuad f`), the commutation being applied on the open box `Q0`. -/
theorem Dth_mixed_open {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hquad : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h1 : Function.uncurry
      (Work.Spaces.DzIter b (Work.Spaces.DthIter 1 (Work.Spaces.DthIter a f))) (z, θ)
      = Function.uncurry
        (Work.Spaces.DthIter 1 (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) (z, θ) :=
    (Work.FTS.H2.DzIter_DthIter_comm_quad Work.FTS.EllipticEst.isOpen_Q0
      (Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0 hF a) b 1) hquad
  simpa only [Function.uncurry, Work.Spaces.mixed, Work.Spaces.DthIter_succ,
    Work.Spaces.DthIter_zero] using h1.symm

/-- **The radial Hardy inequality applied to the `θ`-slice of a mixed derivative, open form.**
This is `Work.FTS.H2.mixed_slice_hardyZ` with `SmoothOpen f`; only the `z`-smoothness of the
slice on `(0,∞)` and the `z → ∞` clause of `BdryTraces` are used. -/
theorem mixed_slice_hardyZ_open (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 4 f) (j i : ℕ) (hij : i + j ≤ 4) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : IntegrableOn (fun z => (Work.Spaces.mixed (j + 1) i f z σ) ^ 2
      * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Spaces.mixed j i f z σ) ^ 2
      ≤ ∫ s in Work.Spaces.Iz, (Work.Spaces.mixed (j + 1) i f s σ) ^ 2
        * (Work.Spaces.w s) ^ 2 := by
  have hcd : ContDiffOn ℝ 1 (fun z => Work.Spaces.mixed j i f z σ) (Set.Ioi (0 : ℝ)) :=
    ((hF.mixed j i).curry_z hσ).of_le (by simp [Work.Stability.smoothOrder])
  have hdec : Tendsto (fun z => Work.Spaces.mixed j i f z σ) atTop (𝓝 0) :=
    Work.FTS.H2.tendsto_atTop_zero_of_traces ((hbd i j hij).1 σ hσ |>.2)
  intro z hz
  exact Work.FTS.H2.hardyZ_open hcd hdec hint z hz

/-- **The interior `L^∞`-`ℋ⁴` trade-off with the sharp constant `10` on the open class.**

For `f` of class `SmoothOpen` (C^∞ on `z > 0`), `ℋ⁴`-honest and with the `BdryTraces`-vanishing
up to order `4`, every mixed derivative `D_z^bD_θ^a f` with `a + b ≤ 2` is bounded at each point
of the open quadrant `Q0` by `10/√(γ-1) · |f|_{ℋ⁴}`.

This is the body of `Work.FTS.H2.mixed_supAbsO_le` (whose hypotheses are the stronger
`SmoothQuad` = C^∞ on `z > -1` and `RegQ α 4 f`) re-run with `SmoothOpen`, using the three
open-quadrant ingredients `HardyThetaOpen`, `slotM_open`, `integrableOn_pth_mixed_sq_sin`
and the already-open `Work.FTS.H2.hardyZ_open`. -/
theorem mixed_abs_le_of_smoothOpen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 4 f) (b a : ℕ) (hab : a + b ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.Spaces.HkNorm α 4 f := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγne : Work.Spaces.gam α ≠ 0 := ne_of_gt (by linarith : 0 < Work.Spaces.gam α)
  obtain ⟨hTle, hTint, hTae⟩ :=
    slotM_open α f hF hmem (b + 1) (a + 1) (by omega) (by omega)
  have hptslot : ∀ σ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      (Work.Spaces.mixed (b + 1) (a + 1) f z σ * Work.Spaces.Wt α z σ) ^ 2
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ((Work.Spaces.mixed (b + 1) (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro σ hσ z
    rw [show Work.Spaces.Wt α z σ
        = Work.Spaces.w z * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) from rfl,
      mul_pow, Work.FTS.H2.Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Work.Spaces.Iz,
    (Work.Spaces.mixed (b + 1) (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      fun σ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with σ _ hσI
    rw [hBdef]
    have hstep : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (∫ z in Work.Spaces.Iz,
              (Work.Spaces.mixed (b + 1) (a + 1) f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun z _ => (hptslot σ hσI z).symm
    exact hstep
  have hTint' : Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      (volume.restrict Work.Spaces.Iθ) := hTint.congr hBae.symm
  set T : ℝ := ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ with hTdef
  have hTle' : T ≤ Work.Spaces.HkSq α 4 f := by
    rw [hTdef]
    rw [show (∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
        = ∫ σ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f z σ * Work.Spaces.Wt α z σ) ^ 2
        from integral_congr_ae hBae]
    exact hTle
  have hKnn : 0 ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the pointwise bound, at the given `(z,θ)`
  have hlim0 : Tendsto (fun θ' => Work.Spaces.mixed b a f z θ')
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
    Work.FTS.H2.tendsto_nhdsGT_zero_of_traces α hα
      ((hbd a b (by omega)).2 z (Set.mem_Ioi.mpr hz) |>.1)
  have hint_ang : IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    integrableOn_pth_mixed_sq_sin (α := α) hα hα1 hF hmem b a hab hz
  have hDth_int2 : IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ) ^ 2) Work.Spaces.Iθ := by
    refine hint_ang.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    show (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ) ^ 2
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (Work.Spaces.mixed b a f) z σ hσ]
    ring
  have hHT := HardyThetaOpen (α := α) hα hα1 (Work.Spaces.mixed b a f) z (hF.mixed b a) hz
    hlim0 hint_ang θ ⟨hθ0, hθ1⟩
  have hI1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    show (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ) ^ 2
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (Work.Spaces.mixed b a f) z σ hσ]
    ring
  have hrad : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · have hsin0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hσpos, hσlt⟩
      rw [Dth_mixed_open hF b a hz hσ']
      exact mul_le_mul_of_nonneg_left
        (mixed_slice_hardyZ_open α f hF hbd b (a + 1) (by omega) hσ' hσint z
          (Set.mem_Ioi.mpr hz))
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
  have hIntLe : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) ≤ T := by
    rw [hI1, hTdef]
    exact integral_mono_ae hDth_int2 hTint' hrad
  have hfin : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (100 / (Work.Spaces.gam α - 1)) * T :=
    le_trans hHT (mul_le_mul_of_nonneg_left hIntLe hKnn)
  -- the constant
  have h1 : Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * T)
      ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTle' hKnn)
  have hsqrt : Real.sqrt (100 / (Work.Spaces.gam α - 1))
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) := by
    have h2 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h2]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  have hfinal : Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f)
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul hKnn, hsqrt]
    simp only [Work.Spaces.HkNorm]
  calc |Work.Spaces.mixed b a f z θ|
      = Real.sqrt ((Work.Spaces.mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * T) := Real.sqrt_le_sqrt hfin
    _ ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f) := h1
    _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := hfinal


end Work.FTS.StrongEps.SupPort
end
end
