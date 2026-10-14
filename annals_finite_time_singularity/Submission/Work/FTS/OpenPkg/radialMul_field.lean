import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.H2.WPQ.m_term_le_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlinear.RadialProd
open Work.FTS.EllipticEst (SmoothOpen Q0)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The open class is closed under multiplication by a radial factor -/

/-- The product of a `SmoothOpen` radial factor with a `SmoothOpen` function is `SmoothOpen`. -/
theorem smoothOpen_sepMul {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => r z * g z θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => r p.1) Q0 := hr
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => g p.1 p.2) Q0 := hg
  exact h1.mul h2

/-! ## The Leibniz rules for a radial factor in the open class -/

/-- The `D_z`-Leibniz rule for a radial factor in the open class. -/
theorem leibniz_rad_Dz (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g) (j : ℕ) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ) := by
  intro z hz θ hθ
  rw [ProdOpen.leibniz_open_Dz j (fun z _ => r z) g hr hg z θ hz hθ.1 hθ.2]
  exact Finset.sum_congr rfl fun b _ => by rw [Work.Elliptic.DzIter_rad]

/-- The mixed Leibniz rule for a radial factor in the open class: all the `D_θ`-derivatives
fall on `g`. -/
theorem leibniz_rad_mixed (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g) (j i : ℕ) (hi : 1 ≤ i) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ) := by
  intro z hz θ hθ
  rw [ProdOpen.leibniz_open_mixed j i (fun z _ => r z) g hr hg z θ hz hθ.1 hθ.2]
  have hzero : ∀ a ∈ Finset.range (i + 1), a ≠ 0 →
      (∑ b ∈ Finset.range (j + 1), ((i.choose a : ℝ) * (j.choose b : ℝ))
        * (Work.Spaces.mixed b a (fun z _ => r z) z θ
            * Work.Spaces.mixed (j - b) (i - a) g z θ)) = 0 := by
    intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show Work.Spaces.mixed b a (fun z _ => r z) z θ = 0 from
      congrFun (congrFun (Work.Elliptic.mixed_rad_eq_zero r (by omega)) z) θ]
    ring
  rw [Finset.sum_eq_single 0 hzero
    (by intro h; exact absurd (Finset.mem_range.mpr (by omega)) h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Nat.choose_zero_right, Nat.sub_zero, Work.Spaces.mixed_zero_right,
    Work.Elliptic.DzIter_rad r b z θ]
  ring

/-! ## The radial Hardy bound in the open class -/

/-- Every `D_z`-iterate of a radial `SmoothOpen` function is `C^∞` on `(0,∞)`. -/
theorem contDiffOn_DzdIter_open (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (b : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.Elliptic.DzdIter b r) (Set.Ioi 0) := by
  have h1 := (hr.DzIter b).curry_z (θ := 1) (by
    constructor
    · norm_num
    · linarith [Real.pi_gt_three])
  exact h1.congr (fun z _ => (Work.Elliptic.DzIter_rad r b z 1).symm)

theorem continuousOn_DzdIter_open (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (b : ℕ) :
    ContinuousOn (fun z => Work.Elliptic.DzdIter b r z) (Set.Ioi 0) :=
  (contDiffOn_DzdIter_open r hr b).continuousOn

/-- Strong measurability of the weighted square of a radial `D_z`-iterate on `Iz`. -/
theorem aesm_DzdIter_sq_w_sq_open (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (b : ℕ) :
    AEStronglyMeasurable
      (fun s : ℝ => (Work.Elliptic.DzdIter b r s) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hc := continuousOn_DzdIter_open r hr b
  have hw : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hfun : (fun s : ℝ => (Work.Spaces.w s) ^ 2)
        = fun s : ℝ => ((1 + s) ^ 2 / s ^ 2) ^ 2 := by
      funext s; rw [Work.Spaces.w]
    rw [hfun]
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))).pow 2
  exact Work.H2.T1Q.aesm_Iz_of_continuousOn (hc.pow 2 |>.mul hw)

/-- A single radial slot `(D_z^b r)² w²` is integrable over `Iz`. -/
theorem integrable_DzdIter_sq_open (α : ℝ) (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z))
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z)) (b : ℕ) (hb : b ≤ 4) :
    MeasureTheory.IntegrableOn
      (fun s => (Work.Elliptic.DzdIter b r s) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' (integrable_Rint α r hrm)
    (aesm_DzdIter_sq_w_sq_open r hr b) ?_
  filter_upwards with s
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact Finset.single_le_sum
    (f := fun i => (Work.Elliptic.DzdIter i r s) ^ 2 * (Work.Spaces.w s) ^ 2)
    (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Finset.mem_range.mpr (by omega))

/-- **The radial Hardy bound in the open class.**  For `b ≤ 3` and `z > 0`,
`(D_z^b r z)² ≤ Rr r`: `HardyZQ` (constant `1`, no `γ - 1` loss) applied to the `z`-slice
`D_z^b r`, whose Hardy integrand `(D_z^{b+1} r)²w²` is a slot of the radial density. -/
theorem dzdIter_sq_le_Rr_open (α : ℝ) (r : ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z))
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z))
    (hdec : ∀ b : ℕ, b ≤ 4 → Filter.Tendsto (Work.Elliptic.DzdIter b r) Filter.atTop (nhds 0))
    {b : ℕ} (hb : b ≤ 3) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r := by
  have hb4 : b + 1 ≤ 4 := by omega
  have hcd : ContDiffOn ℝ 1 (Work.Elliptic.DzdIter b r) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_DzdIter_open r hr b).of_le (by simp [Work.Stability.smoothOrder])
  have hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (Work.Elliptic.DzdIter b r) s) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz := by
    have h := integrable_DzdIter_sq_open α r hr hrm (b + 1) hb4
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
  have hH := Work.FTS.H2.HQ.HardyZQ (Work.Elliptic.DzdIter b r) hcd (hdec b (by omega)) hint z
    (Set.mem_Ioi.mpr hz)
  refine le_trans hH ?_
  rw [show MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (s * deriv (Work.Elliptic.DzdIter b r) s) ^ 2 * (Work.Spaces.w s) ^ 2)
      = MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (Work.Elliptic.DzdIter (b + 1) r s) ^ 2 * (Work.Spaces.w s) ^ 2) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd])]
  rw [Rr]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_Rint α r hrm)
    (Filter.Eventually.of_forall fun s => ?_)
  exact Finset.single_le_sum
    (f := fun i => (Work.Elliptic.DzdIter i r s) ^ 2 * (Work.Spaces.w s) ^ 2)
    (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Finset.mem_range.mpr (by omega))

/-! ## The radial Hardy bound for `g` -/

/-- **The radial Hardy inequality for `g` in the open class.**  For `z > 0` and `θ` in the open
angular interval, `(g z θ)² ≤ Qg g θ`. -/
theorem g_sq_le_Qg_open (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun s => psiZ g s θ) Work.Spaces.Iz)
    {z : ℝ} (hz : 0 < z) :
    (g z θ) ^ 2 ≤ Qg g θ := by
  have hcd : ContDiffOn ℝ 1 (fun z => g z θ) (Set.Ioi (0 : ℝ)) :=
    (hg.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have h := Work.FTS.H2.HQ.HardyZQ (fun z => g z θ) hcd hdec hint z (Set.mem_Ioi.mpr hz)
  rw [show Qg g θ = MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
      (fun s => (s * deriv (fun z => g z θ) s) ^ 2 * (Work.Spaces.w s) ^ 2) from rfl]
  exact h

/-! ## The angular `Qg`-integral in the open class -/

/-- Continuity of the uncurried `ψ z θ = (D_z g)² w(z)²` on the open quadrant. -/
theorem continuousOn_psiZ_open (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => psiZ g p.1 p.2) Q0 := by
  have hdz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 g p.1 p.2) Q0 :=
    ((hg.DzIter 1).forall 0).continuousOn
  have hpsi : (fun p : ℝ × ℝ => psiZ g p.1 p.2)
      = fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2 := rfl
  rw [hpsi]
  exact (hdz.pow 2).mul (continuousOn_w_fst.pow 2)

/-- Strong measurability of the uncurried `Ψ = σ · (D_z g)²w²` on the product measure. -/
theorem aesm_PsiZ_prod_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => PsiZ g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => PsiZ g p.1 p.2)
    (continuousOn_smE_snd.mul (continuousOn_psiZ_open g hg))

/-- Integrability of the uncurried `Ψ` on the product measure. -/
theorem integrable_uncurry_PsiZ_open (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (hgm : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => PsiZ g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hAESM := aesm_PsiZ_prod_open α g hg
  refine (MeasureTheory.integrable_prod_iff hAESM).mpr ⟨?_, ?_⟩
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | rfl
    · have hθcont : ContinuousOn (fun θ : ℝ => PsiZ g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        have h1 : ContinuousOn (fun θ : ℝ => smE θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
          have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
          have h := hsin.rpow_const (p := -(Work.Spaces.eta))
            (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hθ)))
          simpa only [smE] using h
        have h2 : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter 1 g z θ)
            (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
          ((hg.DzIter 1).curry_θ (z := z) hzpos).continuousOn
        exact h1.mul ((h2.pow 2).mul continuousOn_const)
      refine MeasureTheory.Integrable.mono' (hgm.1 z hz)
        (Work.H2.T1Q.aesm_Iθ_of_continuousOn hθcont) ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      simp only [PsiZ]
      rw [Real.norm_of_nonneg (mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ))]
      exact PsiZ_le_HkIntegrand α g hθ
    · have hzero : (fun θ : ℝ => PsiZ g 0 θ) = fun _ => (0 : ℝ) := by
        funext θ
        rw [PsiZ, psiZ]
        simp [Work.Spaces.w]
      rw [hzero]
      exact integrable_zero _ _ _
  · refine MeasureTheory.Integrable.mono' hgm.2 ((hAESM.norm).integral_prod_right') ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => norm_nonneg _) (hgm.1 z hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show ‖PsiZ g z θ‖ ≤ Work.Spaces.HkIntegrand α 4 g z θ
    simp only [PsiZ]
    rw [Real.norm_of_nonneg (mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ))]
    exact PsiZ_le_HkIntegrand α g hθ

/-- The Fubini swap for `Ψ`. -/
theorem PsiZ_swap_open (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (hgm : Work.Spaces.HkMem α 4 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, PsiZ g z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, PsiZ g z θ :=
  MeasureTheory.integral_integral_swap (f := fun z θ => PsiZ g z θ)
    (integrable_uncurry_PsiZ_open α g hg hgm)

/-- **The `Qg`-integral bound in the open class**: `θ ↦ σ θ · Qg g θ` is integrable on `Iθ`
and its integral is at most `HkSq α 4 g` (the single `ℋ⁴`-slot `(D_z g)²w²σ` of `g`). -/
theorem integrable_smE_Qg_le_open (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (hgm : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (fun θ => smE θ * Qg g θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ ≤ Work.Spaces.HkSq α 4 g := by
  have hIntPsi := integrable_uncurry_PsiZ_open α g hg hgm
  have hswap := PsiZ_swap_open α g hg hgm
  have hpts : ∀ θ, (∫ z in Work.Spaces.Iz, PsiZ g z θ) = smE θ * Qg g θ := fun θ => by
    rw [Qg_def_eq g θ, ← MeasureTheory.integral_const_mul]
    rfl
  have hle : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, PsiZ g z θ)
      ≤ Work.Spaces.HkSq α 4 g := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ)))) hgm.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    exact MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (smE_nonneg hθ) (psiZ_nonneg g z θ)))
      (hgm.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => PsiZ_le_HkIntegrand α g hθ))
  refine ⟨?_, ?_⟩
  · have h := MeasureTheory.Integrable.integral_prod_right
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun p : ℝ × ℝ => PsiZ g p.1 p.2) hIntPsi
    rw [show (fun θ => ∫ z, PsiZ g z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) = fun θ => smE θ * Qg g θ from
      funext hpts] at h
    exact h
  · rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => (hpts θ).symm),
      ← hswap]
    exact hle

/-! ## The pointwise majorant for the product -/

/-- The universal constant of the pointwise product bound, extracted from
`Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform`. -/
noncomputable def prodK : ℝ :=
  Classical.choose (Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform)

theorem prodK_pos : 0 < prodK :=
  (Classical.choose_spec
    (Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform)).1

/-- The pointwise product bound with the constant `prodK`, in the exact shape of the backing
theorem. -/
theorem prodK_bound {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b R z) ^ 2 ≤ M)
    (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i - b) h z θ))
    (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j - b) i h z θ))
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hz : 0 < z)
    (hQh : ∀ z' ∈ Set.Ioi (0 : ℝ), (h z' θ) ^ 2 ≤ Qg h θ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ
      ≤ prodK * (M * Work.Spaces.HkIntegrand α 4 h z θ
          + (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2
            * smE θ * Qg h θ) :=
  (Classical.choose_spec
    (Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform)).2
      hM0 hM hDz hMx hθ hz hQh

/-- **The pointwise majorant for the radial product, open class.** -/
theorem hkIntegrand_prod_le_open (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g)
    (hI : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hz : 0 < z)
    (hQg : ∀ z' ∈ Set.Ioi (0 : ℝ), (g z' θ) ^ 2 ≤ Qg g θ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ
      ≤ prodK * (Rr r * Work.Spaces.HkIntegrand α 4 g z θ
          + (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2
            * smE θ * Qg g θ) :=
  prodK_bound (Rr_nonneg r) hI
    (fun i _ z hz θ hθ => leibniz_rad_Dz r g hr hg i z hz θ hθ)
    (fun i j hi hij z hz θ hθ => leibniz_rad_mixed r g hr hg j i hi z hz θ hθ)
    hθ hz hQg

/-! ## The `z`-slice bound and the integrated bound -/

/-- The angular-slice bound at a fixed `z > 0`. -/
theorem slice_le_open (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g)
    (hI : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    (hK3 : MeasureTheory.IntegrableOn (fun θ => smE θ * Qg g θ) Work.Spaces.Iθ)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Qg g θ)
    (hgm : Work.Spaces.HkMem α 4 g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
      ≤ prodK * Rr r * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hstep1 : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (prodK * Rr r * Work.Spaces.HkIntegrand α 4 g z θ
          + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((hgm.1 z hzI).const_mul _ |>.add (hK3.const_mul _)) ?_
    filter_upwards [hQg, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hQ hθ
    exact (hkIntegrand_prod_le_open α r g hr hg hI hθ hz hQ).trans (le_of_eq (by ring))
  have hstep2 : (∫ θ in Work.Spaces.Iθ,
        (prodK * Rr r * Work.Spaces.HkIntegrand α 4 g z θ
          + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)))
      = prodK * Rr r * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
    rw [MeasureTheory.integral_add ((hgm.1 z hzI).const_mul _) (hK3.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hstep2] at hstep1
  exact hstep1

/-- **The `ℋ⁴`-bound for the radial product in the open class**, integrated. -/
theorem HkSq_prod_le_open (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g)
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z)) (hgm : Work.Spaces.HkMem α 4 g)
    (hI : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    (hK3 : MeasureTheory.IntegrableOn (fun θ => smE θ * Qg g θ) Work.Spaces.Iθ)
    (hK3le : ∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ ≤ Work.Spaces.HkSq α 4 g)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Qg g θ) :
    Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ 2 * prodK * Rr r * Work.Spaces.HkSq α 4 g := by
  have hPint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := integrable_DzdIter_sq_open α r hr hrm 4 (by norm_num)
  have hPle : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Rr r := by
    rw [Rr]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (integrable_Rint α r hrm) (Filter.Eventually.of_forall fun z => ?_)
    exact Finset.single_le_sum
      (f := fun i => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_range.mpr (by norm_num))
  have hRnn : 0 ≤ Rr r := Rr_nonneg r
  have hK3nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ :=
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc (fun θ hθ => mul_nonneg (smE_nonneg hθ) (Qg_nonneg g θ)))
  set G : ℝ → ℝ := fun z => prodK * Rr r * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) with hG
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hG]
    exact (hgm.2.const_mul _).add ((hPint.const_mul _).mul_const _)
  have hmono : Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ) ≤ ∫ z in Work.Spaces.Iz, G z := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hGint ?_
    have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    rw [← hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [hG]
    exact slice_le_open α r g hr hg hI hK3 hQg hgm hz
  have hval : (∫ z in Work.Spaces.Iz, G z) = prodK * Rr r * Work.Spaces.HkSq α 4 g
      + prodK * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
    rw [hG]
    simp only []
    rw [MeasureTheory.integral_add (hgm.2.const_mul _) ((hPint.const_mul _).mul_const _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hval] at hmono
  have hPK : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) ≤ Rr r * Work.Spaces.HkSq α 4 g :=
    mul_le_mul hPle hK3le hK3nn hRnn
  have hPK2 : prodK * ((∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ))
      ≤ prodK * (Rr r * Work.Spaces.HkSq α 4 g) :=
    mul_le_mul_of_nonneg_left hPK (le_of_lt prodK_pos)
  nlinarith [hmono, hPK2, hRnn, (HkSq_nonneg α 4 g)]

/-- **The honesty of the radial product in the open class**: `r · g ∈ ℋ⁴`. -/
theorem hkMem_prod_open (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g)
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z)) (hgm : Work.Spaces.HkMem α 4 g)
    (hI : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r)
    (hK3 : MeasureTheory.IntegrableOn (fun θ => smE θ * Qg g θ) Work.Spaces.Iθ)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Qg g θ) :
    Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) := by
  have hrg : SmoothOpen (fun z θ => r z * g z θ) := smoothOpen_sepMul hr hg
  have hPint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := integrable_DzdIter_sq_open α r hr hrm 4 (by norm_num)
  set G : ℝ → ℝ := fun z => prodK * Rr r * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) with hG
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hG]
    exact (hgm.2.const_mul _).add ((hPint.const_mul _).mul_const _)
  constructor
  · intro z hz
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | rfl
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        Work.H2.T1Q.aesm_Iθ_of_continuousOn
          ((hrg.continuousOn_HkIntegrand α 4).comp
            ((continuous_const.prodMk continuous_id).continuousOn)
            (fun θ hθ => ⟨hzpos, hθ⟩))
      have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => prodK * Rr r
            * Work.Spaces.HkIntegrand α 4 g z θ
          + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)) Work.Spaces.Iθ :=
        ((hgm.1 z hz).const_mul _).add (hK3.const_mul _)
      refine MeasureTheory.Integrable.mono' hInt haesm ?_
      filter_upwards [hQg, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hQ hθ
      rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
      exact (hkIntegrand_prod_le_open α r g hr hg hI hθ hzpos hQ).trans (le_of_eq (by ring))
    · have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) 0 θ)
          = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      rw [hzero]
      exact integrableOn_zero
  · have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) p.1 p.2)
        (hrg.continuousOn_HkIntegrand α 4)).integral_prod_right'
    refine MeasureTheory.Integrable.mono' hGint haesm ?_
    have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    rw [← hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
    rw [hG]
    exact slice_le_open α r g hr hg hI hK3 hQg hgm hz

/-! ## The main theorem -/

theorem radialMul_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (r : ℝ → ℝ) (g : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0)
        Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => r z * g z θ)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z _ => r z) * Work.FTS.Nonlin.Xn α g := by
  refine ⟨2 * prodK + 1, by linarith [prodK_pos], ?_⟩
  intro α hα hα1 r g hr hg hrm hgm hdecr hdecg
  have hdecr' : ∀ b : ℕ, b ≤ 4 →
      Filter.Tendsto (Work.Elliptic.DzdIter b r) Filter.atTop (nhds 0) := by
    intro b hb
    have h := hdecr b hb
    simpa only [Work.Elliptic.DzIter_rad] using h
  have hI : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ Rr r :=
    fun b hb z hz => dzdIter_sq_le_Rr_open α r hr hrm hdecr' hb hz
  have hK3 := integrable_smE_Qg_le_open α g hg hgm
  have hQg_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Qg g θ := by
    obtain ⟨-, -, hslice⟩ := Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α g hg hgm
    filter_upwards [hslice, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hint hθ
    intro z hz
    have hintpsi : MeasureTheory.IntegrableOn (fun s => psiZ g s θ) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hint ?_ ?_
      · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
        exact (continuousOn_psiZ_open g hg).comp
          ((continuous_id.prodMk continuous_const).continuousOn)
          (fun s hs => ⟨hs, hθ⟩)
      · filter_upwards with s
        rw [Real.norm_of_nonneg (psiZ_nonneg g s θ)]
        exact psiZ_le_HkIntegrand_of_Ioo α g hθ s
    exact g_sq_le_Qg_open g hg hθ (hdecg 0 (by norm_num) θ hθ) hintpsi hz
  have hmem_prod := hkMem_prod_open α r g hr hg hrm hgm hI hK3.1 hQg_ae
  have hsq := HkSq_prod_le_open α r g hr hg hrm hgm hI hK3.1 hK3.2 hQg_ae
  refine ⟨hmem_prod, ?_⟩
  have hRle : Rr r ≤ Work.Spaces.HkSq α 4 (fun z θ => r z) := Rr_le_HkSq α r
  have hDnn : 0 ≤ Work.Spaces.HkSq α 4 g := HkSq_nonneg α 4 g
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ (Real.sqrt (2 * prodK) * Real.sqrt (Rr r)
          * Real.sqrt (Work.Spaces.HkSq α 4 g)) ^ 2 := by
    have hP : (0 : ℝ) ≤ 2 * prodK := by linarith [prodK_pos]
    rw [mul_pow, mul_pow, Real.sq_sqrt hP, Real.sq_sqrt (Rr_nonneg r), Real.sq_sqrt hDnn]
    exact hsq
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at h2
  have h3 : Real.sqrt (Rr r) ≤ Work.Spaces.HkNorm α 4 (fun z θ => r z) := by
    simp only [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hRle
  have h4 : Real.sqrt (2 * prodK) ≤ 2 * prodK + 1 := by
    have hle : 2 * prodK ≤ (2 * prodK + 1) ^ 2 := by
      nlinarith [prodK_pos, sq_nonneg prodK]
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by linarith [prodK_pos] : (0 : ℝ) ≤ 2 * prodK + 1)] at h
  show Work.FTS.Nonlin.Xn α (fun z θ => r z * g z θ)
      ≤ (2 * prodK + 1) * Work.FTS.Nonlin.Xn α (fun z _ => r z) * Work.FTS.Nonlin.Xn α g
  simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ))
      ≤ Real.sqrt (2 * prodK) * Real.sqrt (Rr r) * Real.sqrt (Work.Spaces.HkSq α 4 g) := h2
    _ ≤ (2 * prodK + 1) * Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => r z))
          * Real.sqrt (Work.Spaces.HkSq α 4 g) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul h4 h3 (Real.sqrt_nonneg _) (by linarith [prodK_pos])

end Work.FTS.OpenPkg
