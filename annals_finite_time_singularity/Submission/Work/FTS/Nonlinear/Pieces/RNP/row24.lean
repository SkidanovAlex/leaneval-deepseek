import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.H2.QangAux
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzIter_mixed_mul_rad
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ### Helper 1: the integration step of the radial product estimate

If the `ℋ⁴`-integrand of `R·h` is pointwise dominated (a.e. in `θ`, for every `z > 0`) by
`C·(M·HkIntegrand h + (D_z⁴R)²w²·smE·Qg h)`, then integrating in `(θ,z)` gives
`HkSq (R·h) ≤ C·(M + ∫_z (D_z⁴R)²w²)·HkSq h`. -/
theorem hkSq_prod_le_rad_int {α M C : ℝ} (hC : 0 < C) (hM0 : 0 ≤ M)
    {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hsh : Work.FTS.LocData.SmoothQuad h) (hhm : Work.Spaces.HkMem α 4 h)
    (hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ),
        Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ
          ≤ C * (M * Work.Spaces.HkIntegrand α 4 h z θ
              + (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ))
    (hInt4 : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz) :
    Work.Spaces.HkSq α 4 (fun z θ => R z * h z θ)
      ≤ C * (M + ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * Work.Spaces.HkSq α 4 h := by
  obtain ⟨hQgInt, hQgCh⟩ := Work.FTS.Nonlinear.RadialProd.integrable_smE_Qg_and_le α h hsh hhm
  have hRn0 : 0 ≤ ∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- the inner `θ`-integral estimate, for every `z > 0`
  have hinner : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ)
        ≤ C * (M * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)
              * ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    intro z hz
    have hzpos : 0 < z := hz
    have hHz : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 h z θ) Work.Spaces.Iθ :=
      hhm.1 z (le_of_lt hzpos)
    have hQz : MeasureTheory.Integrable (fun θ =>
        ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hQgInt.const_mul _
    have hIntG : MeasureTheory.Integrable (fun θ =>
        C * (M * Work.Spaces.HkIntegrand α 4 h z θ
          + ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hHz.const_mul M).add hQz).const_mul C
    have hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ
          ≤ C * (M * Work.Spaces.HkIntegrand α 4 h z θ
              + ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
                * (Work.FTS.Nonlinear.RadialProd.smE θ
                  * Work.FTS.Nonlinear.RadialProd.Qg h θ)) :=
      hbd.mono (fun θ hθ => (hθ z hz).trans_eq (by ring))
    have hmono : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * (M * Work.Spaces.HkIntegrand α 4 h z θ
            + ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) :=
      MeasureTheory.integral_mono_of_nonneg
        (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ)
        (g := fun θ => C * (M * Work.Spaces.HkIntegrand α 4 h z θ
            + ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)))
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
        hIntG hb
    have heq : (∫ θ in Work.Spaces.Iθ, C * (M * Work.Spaces.HkIntegrand α 4 h z θ
          + ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ)))
        = C * (M * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)
              * ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
      rw [MeasureTheory.integral_const_mul C,
        MeasureTheory.integral_add (hHz.const_mul M) hQz,
        MeasureTheory.integral_const_mul M (fun θ => Work.Spaces.HkIntegrand α 4 h z θ),
        MeasureTheory.integral_const_mul ((Work.Elliptic.DzdIter 4 R z) ^ 2
          * (Work.Spaces.w z) ^ 2) (fun θ => Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ)]
      ring
    linarith [hmono, heq.le, heq.ge]
  -- the `z`-integrand of the majorant
  set G : ℝ → ℝ := fun z => C * (M * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 h z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg h θ)
        * ((Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)) with hG
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    rw [hG]
    exact ((hhm.2.const_mul M).add (hInt4.const_mul _)).const_mul C
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, G z := by
    refine MeasureTheory.integral_mono_of_nonneg
      (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ)
      (g := G) (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hGint ?_
    have h2 : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] G :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hinner z hz)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))] at h2
    exact h2
  -- numerical evaluation of the majorant integral
  have hGeq : (∫ z in Work.Spaces.Iz, G z)
      ≤ C * (M + ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * Work.Spaces.HkSq α 4 h := by
    have hsplit : (∫ z in Work.Spaces.Iz, G z)
        = C * (M * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 h z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)
              * (∫ z in Work.Spaces.Iz,
                  (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
      rw [hG, MeasureTheory.integral_const_mul C,
        MeasureTheory.integral_add (hhm.2.const_mul M) (hInt4.const_mul _),
        MeasureTheory.integral_const_mul M (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 h z θ),
        MeasureTheory.integral_const_mul (∫ θ in Work.Spaces.Iθ,
          Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ)
          (fun z => (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)]
    rw [hsplit, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have hK : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 h z θ) = Work.Spaces.HkSq α 4 h := rfl
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg h θ)
        * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Work.Spaces.HkSq α 4 h * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 4 R z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul_of_nonneg_right hQgCh hRn0
    rw [hK]
    nlinarith [h2]
  rw [show Work.Spaces.HkSq α 4 (fun z θ => R z * h z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ from rfl]
  exact hmain.trans hGeq

/-! ### Helper 2: the `angmul` interface applied to the scaled profile `c·(-sin²θ)` -/

theorem angMul_scaled {α₂ Ci α c B : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hB : 0 < B) (hcB : c * B = Ci)
    (hSmoothInt : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ)^2)))
    (hbound : ∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ)^2))| ≤ B)
    (hdth : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ|
          ≤ B * Real.sin (2*θ))
    {g : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) (hIoc : α ∈ Set.Ioc 0 α₂) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (-((Real.sin θ)^2)) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (-((Real.sin θ)^2)) * g z θ)
        ≤ Ci * Ci * Work.FTS.Nonlin.Xn α g := by
  have hci : 0 < Ci := hN.pos.1
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    nlinarith [hci, hB]
  have hO : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.H2.SmoothQuad.toSmoothOpen hsm
  have hSI : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) := by
    constructor
    · change ContDiffOn ℝ ⊤ (fun x : ℝ × ℝ => c * -Real.sin x.2 ^ 2)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
      exact (contDiffOn_const (𝕜 := ℝ) (c := c)).mul hSmoothInt.1
    · intro θ hθ
      simpa only [Pi.mul_apply] using
        (contDiffOn_const (𝕜 := ℝ) (c := c)).mul (hSmoothInt.2 θ hθ)
  have hb1 : ∀ θ ∈ Work.Spaces.Iθ, |c * (-((Real.sin θ)^2))| ≤ Ci := by
    intro θ hθ
    rw [abs_mul, abs_of_pos hc]
    calc c * |(-((Real.sin θ)^2))| ≤ c * B := mul_le_mul_of_nonneg_left (hbound θ hθ) hc.le
      _ = Ci := hcB
  have hb2 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) 0 θ|
        ≤ Ci * Real.sin (2*θ) := by
    intro i hi1 hi4 θ hθ
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul i c
      (fun _ (θ : ℝ) => -((Real.sin θ)^2))]
    rw [abs_mul, abs_of_pos hc]
    calc c * |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ|
        ≤ c * (B * Real.sin (2*θ)) := mul_le_mul_of_nonneg_left (hdth i hi1 hi4 θ hθ) hc.le
      _ = Ci * Real.sin (2*θ) := by rw [← hcB]; ring
  exact hN.angmul α hIoc (fun θ => c * (-((Real.sin θ)^2))) g hSI hb1 hb2 hO hmem

/-! ### Helper 3: the bound on the `D_z⁴`-slot of the radial factor -/

/-- `∫_θ Ktheta θ² ≤ 9·(π/2)`: since `|Ktheta θ| ≤ 3` on `Iθ`. -/
theorem Ktheta_sq_integral_le :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) ≤ 9 * (Real.pi / 2) := by
  have h1 : ∀ θ ∈ Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 ≤ 9 := by
    intro θ hθ
    have hs : (Real.sin θ) ^ 2 ≤ 1 := by
      have h := Real.abs_sin_le_one θ
      nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
    have hc : (Real.cos θ) ^ 2 ≤ 1 := by
      have h := Real.abs_cos_le_one θ
      nlinarith [abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
    rw [Work.Elliptic.Ktheta]
    nlinarith [hs, hc, sq_nonneg (Real.cos θ ^ 2), sq_nonneg (Real.sin θ)]
  have h2 : (∫ θ in Work.Spaces.Iθ, (9 : ℝ)) = 9 * (Real.pi / 2) := by
    have hfun : (fun _ : ℝ => (9 : ℝ)) = fun θ : ℝ => 9 * (1 : ℝ) := by funext θ; ring
    rw [hfun, MeasureTheory.integral_const_mul,
      Work.FTS.Nonlinear.RadialProd.integral_one_Iθ]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (9 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h1)
    |>.trans (le_of_eq h2)

theorem Rn_le {α₂ Ci α : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    {g : Work.FTS.Galerkin.Fn} (hsh : Work.FTS.LocData.SmoothQuad g)
    (hhmem : Work.Spaces.HkMem α 4 g) (hα1 : α ≤ 1) (hIoc : α ∈ Set.Ioc 0 α₂) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
        ≤ (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g := by
  have hαpos : 0 < α := hIoc.1
  obtain ⟨hint, hbound⟩ := Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral hαpos hα1
    hsh hhmem (i := 4) (by norm_num)
  have hFK : Work.Construction.FK g = fun z => Work.Elliptic.Qang g 0 z := by
    funext z
    rw [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Elliptic.Ktheta_eq_K]
    ring
  have hae := Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae hsh hhmem
  have hcongr' : (fun z => (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))]
      (fun z => (Work.Elliptic.Qang g 4 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
      (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.Qang g 4 z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [hae, MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz1 hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    rw [hFK, hz1 hzpos 4 (Finset.mem_range.mpr (by norm_num))]
  have hcongr : (fun z => (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (Work.Elliptic.Qang g 4 z) ^ 2 * (Work.Spaces.w z) ^ 2) := hcongr'
  refine ⟨hint.congr hcongr.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hcongr]
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_right Ktheta_sq_integral_le
    (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)

/-! ### Helper 4: the uniform sup bound for the `D_z`-iterates of the radial factor -/

theorem M_bound {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hdec : ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0)) :
    ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter b (Work.Construction.FK g) z) ^ 2
        ≤ (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g := by
  intro b hb z hz
  rw [RNP24.dzdIter_FK_eq_qang hsm hmem b hb z hz]
  exact (Work.FTS.Nonlinear.Pieces.Qang_sq_le_const α hsm hmem hdec (i := b) hb hz).trans
    (mul_le_mul_of_nonneg_right Ktheta_sq_integral_le
      (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g))

/-! ### Helper 5: the main assembly (conditional on the two remaining interfaces) -/

theorem row24_of_pieces {B C₂ : ℝ} (hBpos : 0 < B) (hC₂pos : 0 < C₂)
    (hSmoothInt : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ)^2)))
    (hbound : ∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ)^2))| ≤ B)
    (hdth : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ|
          ≤ B * Real.sin (2*θ))
    (h6 : ∀ {α M : ℝ}, 0 ≤ M → ∀ {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
      (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
      (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
      (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0:ℝ),
        ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (j+1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j-b) i h z θ))
      {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z)
      (hQh : ∀ z' ∈ Set.Ioi (0:ℝ), (h z' θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ),
      Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ
        ≤ C₂ * (M * Work.Spaces.HkIntegrand α 4 h z θ
            + (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
              * Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ))
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g)
        ≤ K * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨hCi, -⟩ := hN.pos
  refine ⟨(B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) + 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHk : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  -- decay of the slices of `g`
  have hdec3 : ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0) := by
    intro i hi θ hθ
    have h := hgal.decay.2 0 i (by omega) θ hθ
    simpa only [Work.Spaces.mixed_zero_right] using h
  have hdec0 : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0) := by
    intro θ hθ
    have h := hdec3 0 (by norm_num) θ hθ
    simpa only [Work.Spaces.DzIter_zero] using h
  -- the scaled angular profile and `h = c·(-sin²θ)·g`
  set c : ℝ := Ci / B with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcB : c * B = Ci := by rw [hc]; field_simp
  obtain ⟨hmem_h, hXn_h⟩ :=
    angMul_scaled hN hBpos hcB hSmoothInt hbound hdth hsm hmem4 hIoc
  set h : ℝ → ℝ → ℝ := fun z θ => c * (-((Real.sin θ)^2)) * g z θ with hh
  have hsh : Work.FTS.LocData.SmoothQuad h := by
    rw [hh]
    exact Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.LocData.smoothQuad_const_mul c (hSmoothInt.1.of_le le_top)) hsm
  -- the radial factor `FK g`
  have hR4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0:ℝ)) :=
    RNP24.fk_contDiffOn_four hα hα1 hsm hmem6
  obtain ⟨hDz, hMx⟩ := RNP24.dzIter_mixed_mul_rad hR4 hsh
  have hMbound : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ),
      (Work.Elliptic.DzdIter b (Work.Construction.FK g) z) ^ 2
        ≤ (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g :=
    M_bound hsm hmem4 hdec3
  obtain ⟨hRnInt, hRnLe⟩ := Rn_le hN hsm hmem4 hα1 hIoc
  -- the a.e. `Qg`-domination of `h`
  have hQh_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) →
      ∀ z' ∈ Set.Ioi (0:ℝ), (h z' θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    obtain ⟨-, -, hsliceae⟩ := Work.H2.T1Q.HkSqSwapQ α h hsh hmem_h
    filter_upwards [hsliceae, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hslice hθ
    intro _ z' hz'
    have hint : MeasureTheory.IntegrableOn
        (fun s => Work.FTS.Nonlinear.RadialProd.psiZ h s θ) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hslice ?_ ?_
      · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
        have h1 : ContinuousOn (fun s : ℝ => Work.Spaces.DzIter 1 h s θ) (Set.Ioi (0:ℝ)) :=
          ((hsh.DzIter 1).curry_z hθ).continuousOn.mono
            (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
        have h2 : ContinuousOn (fun s : ℝ => Work.Spaces.w s) (Set.Ioi (0:ℝ)) := by
          unfold Work.Spaces.w
          refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
            (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))
        exact (h1.pow 2).mul (h2.pow 2)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s _ => ?_)
        rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.psiZ_nonneg h s θ)]
        exact Work.FTS.Nonlinear.RadialProd.psiZ_le_HkIntegrand_of_Ioo α h hθ s
    have hdec : Filter.Tendsto (fun z => h z θ) Filter.atTop (nhds 0) := by
      have hg0 := hdec0 θ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      have h2 : Filter.Tendsto (fun z => (c * (-((Real.sin θ)^2))) * g z θ)
          Filter.atTop (nhds 0) := by
        simpa only [mul_zero] using hg0.const_mul (c * (-((Real.sin θ)^2)))
      have h1 : (fun z => h z θ) = fun z => (c * (-((Real.sin θ)^2))) * g z θ := by
        funext z; rw [hh]
      rw [h1]
      exact h2
    exact Work.FTS.Nonlinear.RadialProd.g_sq_le_Qg (g := h) (hsq := hsh) (hθ := hθ)
      (hdec := hdec) (hint := hint) (z := z') (hz := hz')
  -- the pointwise integrand bound
  set M : ℝ := (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by positivity) (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)
  have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0:ℝ),
        Work.Spaces.HkIntegrand α 4 (fun z θ => Work.Construction.FK g z * h z θ) z θ
          ≤ C₂ * (M * Work.Spaces.HkIntegrand α 4 h z θ
              + (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ) := by
    filter_upwards [hQh_ae, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ hθI
    intro z hz
    exact h6 hM0 hMbound hDz hMx hθI hz (fun z' hz' => hθ hθI z' hz')
  -- the product estimate
  have hmain := hkSq_prod_le_rad_int (C := C₂) hC₂pos hM0 hsh hmem_h hbd hRnInt
  have hHkh : Work.Spaces.HkSq α 4 h = (Work.FTS.Nonlin.Xn α h) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 h)).symm
  have hMX : M = (9 * (Real.pi / 2)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    rw [hM, hHk]
  have hRn2 : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ (9 * (Real.pi / 2)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (by rw [← hHk]; exact hRnLe)
  have hsum : M + (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ 9 * Real.pi * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    rw [hMX]
    linarith [hRn2]
  have hXh2 : (Work.FTS.Nonlin.Xn α h) ^ 2
      ≤ (Ci * Ci * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h0 : 0 ≤ Ci * Ci * Work.FTS.Nonlin.Xn α g := by
      have := hN.pos.1; positivity
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 h) hXn_h 2
  have hstep : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z * h z θ)
      ≤ (C₂ * (9 * Real.pi * Ci ^ 4)) * (Work.FTS.Nonlin.Xn α g) ^ 4 := by
    refine hmain.trans ?_
    have hA : C₂ * (M + ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 4 h
        ≤ C₂ * (9 * Real.pi * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (Ci * Ci * Work.FTS.Nonlin.Xn α g) ^ 2 := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hsum hC₂pos.le) ?_ ?_ ?_
      · rw [hHkh]
        exact hXh2
      · exact Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 h
      · positivity
    refine hA.trans (le_of_eq ?_)
    ring
  have hXn_final : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * h z θ)
      ≤ Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * h z θ)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z * h z θ)) := rfl
      _ ≤ Real.sqrt ((C₂ * (9 * Real.pi * Ci ^ 4))
            * (Work.FTS.Nonlin.Xn α g) ^ 4) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        rw [Real.sqrt_mul (by positivity),
          show (Work.FTS.Nonlin.Xn α g) ^ 4 = ((Work.FTS.Nonlin.Xn α g) ^ 2) ^ 2 from by ring,
          Real.sqrt_sq (by positivity)]
  have hN5 : Work.FTS.Nonlin.N5gg g
      = fun z θ => c⁻¹ * (Work.Construction.FK g z * h z θ) := by
    funext z θ
    rw [hh, Work.FTS.Nonlin.N5gg]
    field_simp
  rw [hN5, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
    abs_of_pos (by positivity : (0 : ℝ) < c⁻¹)]
  calc c⁻¹ * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * h z θ)
      ≤ c⁻¹ * (Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4))
          * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
        mul_le_mul_of_nonneg_left hXn_final (by positivity)
    _ = (B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4))
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        rw [hc]; field_simp
    _ ≤ ((B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) + 1)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        have h1 : 0 ≤ (B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) := by positivity
        have h2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
        nlinarith [h1, h2]

theorem row24 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g)
        ≤ K * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨B, hBpos, hSmoothInt, hbound, hdth⟩ := RNP24.angProfile_sinSq
  obtain ⟨C₂, hC₂pos, h6⟩ := RNP24.hkIntegrand_prod_le_rad_uniform
  exact row24_of_pieces (α₂ := α₂) (Ci := Ci) (Ct := Ct) (Ce := Ce) (Cs := Cs)
    hBpos hC₂pos hSmoothInt hbound hdth h6 hN

end Work.FTS.Nonlinear.Pieces.RNP
