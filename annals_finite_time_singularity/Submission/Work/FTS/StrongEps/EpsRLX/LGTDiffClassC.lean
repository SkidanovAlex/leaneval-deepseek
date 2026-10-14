import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.hkMem_prod_open_M
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDz_of
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIRho
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.StrongEps.H5.HkMemXnLGammaT5
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothStripDefs
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN5a =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)

/-! ## The angular moment `FK g` is the `D_z`-tower of `Qang g 0` -/

/-- **`D_z^b (FK g) = Qang g b` on `(0,∞)`, for `b ≤ 3`**, in the open-quadrant class
`SmoothOpen g` + `HkMem α 4 g` (no decay, no interior smoothness through `z = 0`).

`FK g = Qang g 0` (the two angular weights agree), and the angular moments satisfy the divided
derivative `(Qang g j)' z = Qang g (j+1) z / z` for `j ≤ 2` pointwise on `(0,∞)`
(`QangOpen.hasDerivAt_Qang_open`), so `DzdIter_eq_of_hasDerivAt'` gives all the iterates up to
`3`. -/
theorem dzdIter_FK_eq_qang_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter b (fun z => Work.Construction.FK g z) z
        = Work.Elliptic.Qang g b z := by
  have hFK : ∀ z : ℝ, Work.Construction.FK g z = Work.Elliptic.Qang g 0 z := by
    intro z
    rw [Work.Construction.FK, Work.Elliptic.Qang]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Elliptic.Ktheta_eq_K]
    simp only [Work.Spaces.DzIter_zero]
    ring
  have hpt : ∀ i ≤ 3, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g i z :=
    fun i hi z hz => Work.FTS.StrongPersist.DzdIter_eq_of_hasDerivAt' 2 (fun _ => rfl)
      (fun j hj z hz => Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α g hO hmem hj hz
        (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem (by omega)))
      i (by omega) z hz
  intro b hb z hz
  rw [Work.FTS.StrongPersist.DzdIter_congr_Ioi (fun y _ => hFK y) b z hz, hpt b hb z hz]

/-! ## The integrated radial-product bound with a constant radial majorant -/

/-- **The `ℋ⁴`-bound for the radial product `r·g` with a constant majorant `M` of the radial
slots `b ≤ 3`.**

This is `Work.FTS.OpenPkg.HkSq_prod_le_open` with the radial quantity `Rr r` of the first term
(the slots `b ≤ 3`) replaced by the caller's constant `M`; the `D_z^4`-slot keeps the sharp
`Rr r`.  The proof is the corresponding one-quantity swap of the slice bound
(`slice_le_open_M`, integrated). -/
theorem HkSq_prod_le_open_M (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (M : ℝ)
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z))
    (hgm : Work.Spaces.HkMem α 4 g)
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ M)
    (hK3 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.Nonlinear.RadialProd.smE θ
        * Work.FTS.Nonlinear.RadialProd.Qg g θ) Work.Spaces.Iθ)
    (hK3le : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
        * Work.FTS.Nonlinear.RadialProd.Qg g θ) ≤ Work.Spaces.HkSq α 4 g)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg g θ) :
    Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ 2 * Work.FTS.OpenPkg.prodK
          * (M + Work.FTS.Nonlinear.RadialProd.Rr r) * Work.Spaces.HkSq α 4 g := by
  have hPint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    Work.FTS.OpenPkg.integrable_DzdIter_sq_open α r hr hrm 4 (by norm_num)
  have hPle : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Work.FTS.Nonlinear.RadialProd.Rr r := by
    rw [Work.FTS.Nonlinear.RadialProd.Rr]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.Nonlinear.RadialProd.integrable_Rint α r hrm)
      (Filter.Eventually.of_forall fun z => ?_)
    exact Finset.single_le_sum
      (f := fun i => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_range.mpr (by norm_num))
  have hRnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.Rr r :=
    Work.FTS.Nonlinear.RadialProd.Rr_nonneg r
  have hHnn : 0 ≤ Work.Spaces.HkSq α 4 g :=
    Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g
  have hK3nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
      * Work.FTS.Nonlinear.RadialProd.Qg g θ :=
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc (fun θ hθ => mul_nonneg
        (Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ)
        (Work.FTS.Nonlinear.RadialProd.Qg_nonneg g θ)))
  set G : ℝ → ℝ := fun z => Work.FTS.OpenPkg.prodK * M * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      + Work.FTS.OpenPkg.prodK
        * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg g θ) with hG
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hG]
    exact (hgm.2.const_mul _).add ((hPint.const_mul _).mul_const _)
  have hmono : Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ ∫ z in Work.Spaces.Iz, G z := by
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
    exact Work.FTS.OpenPkg.slice_le_open_M α r g M hr hg hM hK3 hQg hgm hz
  have hval : (∫ z in Work.Spaces.Iz, G z)
      = Work.FTS.OpenPkg.prodK * M * Work.Spaces.HkSq α 4 g
        + Work.FTS.OpenPkg.prodK * (∫ z in Work.Spaces.Iz,
              (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg g θ) := by
    rw [hG]
    simp only []
    rw [MeasureTheory.integral_add (hgm.2.const_mul _) ((hPint.const_mul _).mul_const _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hval] at hmono
  have hPK : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg g θ)
      ≤ Work.FTS.Nonlinear.RadialProd.Rr r * Work.Spaces.HkSq α 4 g :=
    mul_le_mul hPle hK3le hK3nn hRnn
  have hPK2 : Work.FTS.OpenPkg.prodK * ((∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg g θ))
      ≤ Work.FTS.OpenPkg.prodK * (Work.FTS.Nonlinear.RadialProd.Rr r
          * Work.Spaces.HkSq α 4 g) :=
    mul_le_mul_of_nonneg_left hPK (le_of_lt Work.FTS.OpenPkg.prodK_pos)
  have hM0 : 0 ≤ M :=
    le_trans (sq_nonneg (Work.Elliptic.DzdIter 0 r 1))
      (hM 0 (by norm_num) 1 (Set.mem_Ioi.mpr (by norm_num)))
  have hPKnn : 0 ≤ Work.FTS.OpenPkg.prodK * M * Work.Spaces.HkSq α 4 g :=
    mul_nonneg (mul_nonneg (le_of_lt Work.FTS.OpenPkg.prodK_pos) hM0) hHnn
  have hR2nn : 0 ≤ Work.FTS.OpenPkg.prodK * (Work.FTS.Nonlinear.RadialProd.Rr r
      * Work.Spaces.HkSq α 4 g) :=
    mul_nonneg (le_of_lt Work.FTS.OpenPkg.prodK_pos) (mul_nonneg hRnn hHnn)
  nlinarith [hmono, hPK2, hPKnn, hR2nn, hM0, hRnn, hHnn,
    le_of_lt Work.FTS.OpenPkg.prodK_pos]

/-! ## Row 24 of the honest §8 table -/

theorem rowsN5a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨Cf, hCfpos, hfkH⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Cang, hCangpos, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Bs, hBspos, haSO, haB, haIt⟩ := Work.FTS.StrongEps.EpsZero.ClassCHk.angSq_data
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  set K : ℝ := Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : 0 ≤ Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)) := by
      refine mul_nonneg (mul_nonneg hCangpos.le hBspos.le) (Real.sqrt_nonneg _)
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hgSO : Work.FTS.EllipticEst.SmoothOpen g := hctx.hSmoothOpen
  have hmem4 : Work.Spaces.HkMem α 4 g := hctx.hkMem4
  have h0 : Work.Construction.L12 g 0 = 0 := hctx.hL12
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXsq : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  -- ## the smoothness and the `ℋ⁴`-honesty of the angular moment `FK g`
  have hFKsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK g z) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.so_FKw hctx.hg
  obtain ⟨hFKmem, hFKbd⟩ := hfkH α hα hα1 g ⟨hgSO, hmem4⟩ h0
  -- ## the pointwise bound on the radial slots `b ≤ 3`
  have hpt : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK g z) z) ^ 2
        ≤ K1 * Work.Spaces.HkSq α 4 g := by
    intro b hb z hz
    have hq := Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open (α := α) (g := g)
      hα hα1 hgSO hmem4 (i := b) hb (z := z) hz
    rw [dzdIter_FK_eq_qang_open hgSO hmem4 b hb z hz, hK1def]
    exact hq
  -- ## the a.e. radial Hardy bound for the slices of `g`
  have hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (g z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg g θ := by
    obtain ⟨-, -, hslice⟩ :=
      Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α g hgSO hmem4
    filter_upwards [hslice, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hint hθ
    intro z hz
    have hθI : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0) := by
      have hd := hctx.hdecay.1 0 0 (by norm_num) θ hθI
      simpa using hd
    have hintpsi : MeasureTheory.IntegrableOn
        (fun s => Work.FTS.Nonlinear.RadialProd.psiZ g s θ) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hint ?_ ?_
      · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
        exact (Work.FTS.OpenPkg.continuousOn_psiZ_open g hgSO).comp
          ((continuous_id.prodMk continuous_const).continuousOn) (fun s hs => ⟨hs, hθ⟩)
      · filter_upwards with s
        rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.psiZ_nonneg g s θ)]
        exact Work.FTS.Nonlinear.RadialProd.psiZ_le_HkIntegrand_of_Ioo α g hθ s
    exact Work.FTS.OpenPkg.g_sq_le_Qg_open g hgSO hθ hdec hintpsi hz
  have hK3 := Work.FTS.OpenPkg.integrable_smE_Qg_le_open α g hgSO hmem4
  -- ## the radial product `FK g · g`
  have hmemF : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.FK g z * g z θ) :=
    Work.FTS.OpenPkg.hkMem_prod_open_M α (fun z => Work.Construction.FK g z) g
      (K1 * Work.Spaces.HkSq α 4 g) hFKsm hgSO hFKmem hmem4 hpt hK3.1 hQg
  have hSQ := HkSq_prod_le_open_M α (fun z => Work.Construction.FK g z) g
    (K1 * Work.Spaces.HkSq α 4 g) hFKsm hgSO hFKmem hmem4 hpt hK3.1 hK3.2 hQg
  have hRr : Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z)
      ≤ Cf ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h2 : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z)
        = (Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)) ^ 2 :=
      (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4
        (fun z θ => Work.Construction.FK g z))).symm
    calc Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z)
        ≤ Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z) :=
          Work.FTS.Nonlinear.RadialProd.Rr_le_HkSq α (fun z => Work.Construction.FK g z)
      _ = (Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)) ^ 2 := h2
      _ ≤ (Cf * Work.FTS.Nonlin.Xn α g) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hFKbd 2
      _ = Cf ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
  -- ## the `ℋ⁴`-bound of the radial product
  have hXprod : Work.FTS.Nonlin.Xn α
        (fun z θ => Work.Construction.FK g z * g z θ)
      ≤ Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have hMx : K1 * Work.Spaces.HkSq α 4 g
          + Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z)
        ≤ (K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rw [hXsq]
      nlinarith [hRr]
    have hCnn : 0 ≤ 2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Work.FTS.OpenPkg.prodK_pos))
        (by positivity)
    have hkey : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z * g z θ)
        ≤ (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 4 := by
      refine hSQ.trans ?_
      have hstep : 2 * Work.FTS.OpenPkg.prodK
            * (K1 * Work.Spaces.HkSq α 4 g
              + Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z))
            * Work.Spaces.HkSq α 4 g
          ≤ 2 * Work.FTS.OpenPkg.prodK * ((K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * Work.Spaces.HkSq α 4 g := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMx ?_) ?_
        · exact mul_nonneg (by norm_num) (le_of_lt Work.FTS.OpenPkg.prodK_pos)
        · exact Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g
      calc 2 * Work.FTS.OpenPkg.prodK
            * (K1 * Work.Spaces.HkSq α 4 g
              + Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z))
            * Work.Spaces.HkSq α 4 g
          ≤ 2 * Work.FTS.OpenPkg.prodK * ((K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * Work.Spaces.HkSq α 4 g := hstep
        _ = 2 * Work.FTS.OpenPkg.prodK * ((K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (Work.FTS.Nonlin.Xn α g) ^ 2 := by rw [hXsq]
        _ = (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 4 := by ring
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * g z θ)
        = Real.sqrt (Work.Spaces.HkSq α 4
            (fun z θ => Work.Construction.FK g z * g z θ)) := rfl
      _ ≤ Real.sqrt ((2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 4) := Real.sqrt_le_sqrt hkey
      _ = Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
          rw [Real.sqrt_mul hCnn,
            show (Work.FTS.Nonlin.Xn α g) ^ 4
                = ((Work.FTS.Nonlin.Xn α g) ^ 2) ^ 2 from by ring,
            Real.sqrt_sq (by positivity)]
  -- ## the angular factor `-sin²θ`
  have hN5 : Work.FTS.Nonlin.N5gg g
      = fun z θ => (-(Real.sin θ) ^ 2)
          * (Work.Construction.FK g z * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N5gg]
    ring
  obtain ⟨-, hXnang⟩ := hang α hα hα1 (fun θ => -((Real.sin θ) ^ 2))
    (fun z θ => Work.Construction.FK g z * g z θ) Bs haSO haB haIt
    (Work.FTS.OpenPkg.smoothOpen_sepMul hFKsm hgSO) hmemF
  rw [hN5]
  refine hXnang.trans ?_
  have hstep : Cang * Bs * Work.FTS.Nonlin.Xn α
        (fun z θ => Work.Construction.FK g z * g z θ)
      ≤ Cang * Bs * (Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
          * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
    mul_le_mul_of_nonneg_left hXprod (mul_nonneg hCangpos.le hBspos.le)
  refine hstep.trans ?_
  rw [hKdef]
  have hfac : Cang * Bs * (Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
        * (Work.FTS.Nonlin.Xn α g) ^ 2)
      = (Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)))
        * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
  rw [hfac]
  have hSnn : 0 ≤ Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)) := by
    refine mul_nonneg (mul_nonneg hCangpos.le hBspos.le) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (Work.FTS.Nonlin.Xn α g), hSnn]

end Work.FTS.StrongEps.E4R3.N4C.rows
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_p48 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.N_b6_p48` — the level-`6` bounds of the two pieces `NBlk 4` and `NBlk 8`

The two pieces of the level-six `N`-block whose second factor is a *slot* of `w` of order one
above the norm (`(Uop(Phig)/sin 2t)·D_tw` and `-2a·Vop(Phig)·D_zw`).  The mathematics is in
`Tools/shiftProdDth.lean` / `Tools/shiftProdDz_of.lean`; here the two *elliptic* atoms are
instantiated at the hypotheses of the statement:

* `MA`: the pointwise bound `|A| <= C(gam-1)^{-1/2}|A|_{H4}` (`TransportS.sup_dz_le_hk`);
* `KA`: the flat price `|d_t A8| <= Ce a^{-1/2}Xn w` of `EllPkgGo.Vth`;
* `HkSq a 6 A <= Ce^2·HkSq a 6 w` from `EllPkgK`.

The bookkeeping of the constants: with `Gm = (gam a - 1)^{-1} >= 0`, `E := HkSq a 6 w >= 0`,
`E7 := HkSq a 7 w >= 0`, both product bounds give (atoms `A4 = Uop/sin 2t`, `A8 = Vop`)

  `(1 + Gm·(HkSq 6 A4 + E))·(HkSq 6 A4 + E) <= KB·(1+E)^2`,
  `(1 + KA8^2)·(1 + Gm·(HkSq 6 A8 + E))·(HkSq 6 A8 + E) <= KB·(1+E)^2`,

with `KB := (1+KMA)·(1+Ce^2C0^2)·(1+Ce^2)·(1+Gm·(1+Ce^2))` and
`KMA := 1 + Gm·Csup^2·Ce^2·C0^2` — every factor is `>= 1`, so `KB` dominates each of the two
products of factors.  The final constant is `K := (4C4 + 4C8 + 1)·(1 + KMA + KB)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

private theorem absSq_eq (x : ℝ) : |x| ^ 2 = x ^ 2 := by
  rw [pow_two, pow_two, abs_mul_abs_self]

private theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith only [h, ha]

private theorem one_le_mul_aux {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith only [ha, hb]

private theorem sum_le_one_add {a E Ce2 : ℝ} (h : a ≤ Ce2 * E) (hE : 0 ≤ E) (hCe : 0 ≤ Ce2) :
    a + E ≤ (1 + Ce2) * (1 + E) := by
  nlinarith only [h, hE, hCe]

private theorem one_add_mul_le {Gm S E Ce2 : ℝ} (hG : 0 ≤ Gm) (hS : S ≤ (1 + Ce2) * (1 + E))
    (hE : 0 ≤ E) (hC : 0 ≤ Ce2) : 1 + Gm * S ≤ (1 + Gm * (1 + Ce2)) * (1 + E) := by
  nlinarith only [hG, hS, hE, hC]

private theorem mul_sq_le {M K E : ℝ} (h : M ≤ K) (hE : 0 ≤ E) (hK : 0 ≤ K) :
    M * E ≤ K * (1 + E) := by
  nlinarith only [h, hE, hK]

private theorem bracket_le {Gm A E Ce2 KB : ℝ} (hG : 0 ≤ Gm)
    (hfac : 1 + Gm * A ≤ (1 + Gm * (1 + Ce2)) * (1 + E))
    (hsum : A ≤ (1 + Ce2) * (1 + E)) (hA : 0 ≤ A) (hE : 0 ≤ E) (hC : 0 ≤ Ce2)
    (hP : (1 + Ce2) * (1 + Gm * (1 + Ce2)) ≤ KB) :
    (1 + Gm * A) * A ≤ KB * (1 + E) ^ 2 := by
  have hb : (0 : ℝ) ≤ (1 + Gm * (1 + Ce2)) * (1 + E) :=
    mul_nonneg (by nlinarith only [hG, hC]) (by linarith only [hE])
  have h1 : (1 + Gm * A) * A
      ≤ ((1 + Gm * (1 + Ce2)) * (1 + E)) * ((1 + Ce2) * (1 + E)) :=
    mul_le_mul hfac hsum hA hb
  have h2 : ((1 + Gm * (1 + Ce2)) * (1 + E)) * ((1 + Ce2) * (1 + E))
      = ((1 + Ce2) * (1 + Gm * (1 + Ce2))) * (1 + E) ^ 2 := by ring
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right hP (sq_nonneg _))

private theorem bracket_le_KA {Gm A E Ce2 Cq KA2 KB : ℝ} (hG : 0 ≤ Gm)
    (hKA : 1 + KA2 ≤ 1 + Ce2 * Cq) (hfac : 1 + Gm * A ≤ (1 + Gm * (1 + Ce2)) * (1 + E))
    (hsum : A ≤ (1 + Ce2) * (1 + E)) (hA : 0 ≤ A) (hE : 0 ≤ E) (hC : 0 ≤ Ce2)
    (hKA0 : 0 ≤ 1 + KA2) (hCq : 0 ≤ 1 + Ce2 * Cq)
    (hP : (1 + Ce2 * Cq) * ((1 + Ce2) * (1 + Gm * (1 + Ce2))) ≤ KB) :
    (1 + KA2) * (1 + Gm * A) * A ≤ KB * (1 + E) ^ 2 := by
  have hGA : (0 : ℝ) ≤ 1 + Gm * A := by
    have := mul_nonneg hG hA
    linarith only [this]
  have hb : (0 : ℝ) ≤ (1 + Gm * (1 + Ce2)) * (1 + E) :=
    mul_nonneg (by nlinarith only [hG, hC]) (by linarith only [hE])
  have hc : (0 : ℝ) ≤ (1 + Ce2 * Cq) * ((1 + Gm * (1 + Ce2)) * (1 + E)) :=
    mul_nonneg hCq hb
  have h1 : (1 + KA2) * (1 + Gm * A) * A
      ≤ ((1 + Ce2 * Cq) * ((1 + Gm * (1 + Ce2)) * (1 + E))) * ((1 + Ce2) * (1 + E)) :=
    mul_le_mul (mul_le_mul hKA hfac hGA hCq) hsum hA hc
  have h2 : ((1 + Ce2 * Cq) * ((1 + Gm * (1 + Ce2)) * (1 + E))) * ((1 + Ce2) * (1 + E))
      = ((1 + Ce2 * Cq) * ((1 + Ce2) * (1 + Gm * (1 + Ce2)))) * (1 + E) ^ 2 := by ring
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right hP (sq_nonneg _))

private theorem absorb_le {C X A B K1 K2 : ℝ} (hC : 0 ≤ C) (h1 : A ≤ K1) (h2 : B ≤ K2)
    (h : X ≤ C * (A + B)) : X ≤ C * (K1 + K2) :=
  le_trans h (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC)

/-- **The `D_z` shift-product bound**, instantiated at `ptBoundDz`. -/
theorem shiftProdDz (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
      Work.Spaces.HkSq α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ)
        ≤ C * (MA ^ 2 * Work.Spaces.HkSq α 7 f
            + (1 + KA ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f)) :=
  Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDz_of α hα hα1
    (Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDz α hα hα1)

/-- **The level-`6` bounds of the two pieces `NBlk 4` and `NBlk 8`.** -/
theorem N_b6_p48 : Work.FTS.StrongEps.E4R3.Nblock6.P48Stmt := by
  intro C₀ Ce Cs α hαmem
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  obtain ⟨C4, hC4pos, h4⟩ := Work.FTS.StrongEps.E4R3.Nblock6.Tools.shiftProdDth α hα0 hα1
  obtain ⟨C8, hC8pos, h8⟩ := shiftProdDz α hα0 hα1
  obtain ⟨Csup, hCsuppos, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith only [hα0]
  have hGnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  -- ## the constants
  set KMA : ℝ := 1 + (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 with hKMAdef
  have hKMA1 : 1 ≤ KMA := by
    rw [hKMAdef]
    have hnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hGnn (sq_nonneg Csup)) (sq_nonneg Ce)) (sq_nonneg C₀)
    linarith only [hnn]
  have hCe20 : (0 : ℝ) ≤ Ce ^ 2 := sq_nonneg Ce
  have hCq0 : (0 : ℝ) ≤ Ce ^ 2 * C₀ ^ 2 := mul_nonneg hCe20 (sq_nonneg C₀)
  have hCeQ : (0 : ℝ) ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hCq0]
  have hCe1 : (0 : ℝ) ≤ 1 + Ce ^ 2 := by linarith only [hCe20]
  have hGc : (0 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2) :=
    mul_nonneg hGnn hCe1
  set KB : ℝ := (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
      * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) with hKBdef
  have hKB1 : 1 ≤ KB := by
    rw [hKBdef]
    have h1 : (1 : ℝ) ≤ 1 + KMA := by linarith only [hKMA1]
    have h2 : (1 : ℝ) ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hCq0]
    have h3 : (1 : ℝ) ≤ 1 + Ce ^ 2 := by linarith only [hCe20]
    have h4 : (1 : ℝ) ≤ 1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2) := by
      linarith only [hGc]
    have h5 := one_le_mul_aux (one_le_mul_aux h1 h2) (one_le_mul_aux h3 h4)
    calc (1 : ℝ) ≤ ((1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2))
            * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) := h5
      _ = (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) := by ring
  set K : ℝ := (4 * C4 + 4 * C8 + 1) * (1 + KMA + KB) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (by linarith only [hC4pos, hC8pos]) (by linarith only [hKMA1, hKB1])
  -- the data-independent inequalities of the statement
  have hP12 : (1 : ℝ) ≤ (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) := by
    have h1 : (1 : ℝ) ≤ 1 + KMA := by linarith only [hKMA1]
    have h2 : (1 : ℝ) ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hCq0]
    nlinarith only [h1, h2]
  have hP34 : (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) ≤ KB := by
    rw [hKBdef]
    have hx : (0 : ℝ) ≤ (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) :=
      mul_nonneg hCe1 (by linarith only [hGc])
    calc (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))
        = 1 * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) := by ring
      _ ≤ ((1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2))
            * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) :=
          mul_le_mul_of_nonneg_right hP12 hx
      _ = (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) := by ring
  have hP234 : (1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
      * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) ≤ KB := by
    rw [hKBdef]
    have hx : (0 : ℝ) ≤ (1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) :=
      mul_nonneg hCe1 (by linarith only [hGc])
    have hy : (0 : ℝ) ≤ (1 + Ce ^ 2 * C₀ ^ 2)
        * ((1 + Ce ^ 2) * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2))) :=
      mul_nonneg hCeQ hx
    calc (1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
          * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)))
        = 1 * ((1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)))) := by ring
      _ ≤ (1 + KMA) * ((1 + Ce ^ 2 * C₀ ^ 2) * ((1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)))) :=
          mul_le_mul_of_nonneg_right (by linarith only [hKMA1]) hy
      _ = (1 + KMA) * (1 + Ce ^ 2 * C₀ ^ 2) * (1 + Ce ^ 2)
            * (1 + (Work.Spaces.gam α - 1)⁻¹ * (1 + Ce ^ 2)) := by ring
  have hK4KMA : 4 * C4 * KMA ≤ K := by
    rw [hKdef]
    have h1 : 4 * C4 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC8pos]
    have h2 : KMA ≤ 1 + KMA + KB := by linarith only [hKB1]
    exact mul_le_mul h1 h2 (by linarith only [hKMA1]) (by linarith only [hC4pos, hC8pos])
  have hK4KB : 4 * C4 * KB ≤ K := by
    rw [hKdef]
    have h1 : 4 * C4 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC8pos]
    have h2 : KB ≤ 1 + KMA + KB := by linarith only [hKMA1]
    exact mul_le_mul h1 h2 (by linarith only [hKB1]) (by linarith only [hC4pos, hC8pos])
  have hK8KMA : 4 * C8 * KMA ≤ K := by
    rw [hKdef]
    have h1 : 4 * C8 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC4pos]
    have h2 : KMA ≤ 1 + KMA + KB := by linarith only [hKB1]
    exact mul_le_mul h1 h2 (by linarith only [hKMA1]) (by linarith only [hC4pos, hC8pos])
  have hK8KB : 4 * C8 * KB ≤ K := by
    rw [hKdef]
    have h1 : 4 * C8 ≤ 4 * C4 + 4 * C8 + 1 := by linarith only [hC4pos]
    have h2 : KB ≤ 1 + KMA + KB := by linarith only [hKMA1]
    exact mul_le_mul h1 h2 (by linarith only [hKB1]) (by linarith only [hC4pos, hC8pos])
  refine ⟨K, hKpos, ?_⟩
  intro Φs w Φg hw hXw hz' hell hK6 hstar
  -- ## the datum `w`
  have hXwnn : 0 ≤ Work.FTS.Nonlin.Xn α w := Real.sqrt_nonneg _
  have h6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hα2 : α ^ 2 ≤ 1 := by
    have h := pow_le_one₀ hα0.le hα1 (n := 2)
    nlinarith only [h, sq_nonneg α]
  have hXw' : Work.FTS.Nonlin.Xn α w ≤ |C₀| * α ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α w ≤ |C₀ * α ^ 2| := le_trans hXw (le_abs_self _)
    rwa [abs_mul, abs_of_nonneg (sq_nonneg α)] at h1
  have hwsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 := by
    have ha : (0 : ℝ) ≤ |C₀| * α ^ 2 := by positivity
    have hle : |C₀| * α ^ 2 ≤ |C₀| := by nlinarith only [hα2, abs_nonneg C₀]
    have h3 : (|C₀| * α ^ 2) ^ 2 ≤ C₀ ^ 2 := by
      have h := sq_le_sq_of_nonneg ha hle
      simpa only [absSq_eq C₀] using h
    exact le_trans (sq_le_sq_of_nonneg hXwnn hXw') h3
  -- ## the two elliptic atoms
  set A4 : ℝ → ℝ → ℝ := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg)
      z θ / Work.Construction.s2 θ with hA4def
  set A8 : ℝ → ℝ → ℝ := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg) with hA8def
  have hA4sm : Work.FTS.EllipticEst.SmoothOpen A4 := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.1.1
  have hA4mem : Work.Spaces.HkMem α 6 A4 := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.1.2
  have hA4mem4 : Work.Spaces.HkMem α 4 A4 :=
    Work.FTS.OpenPkg.HkMem_mono_open hA4sm 4 (by norm_num) hA4mem
  have hA8sm : Work.FTS.EllipticEst.SmoothOpen A8 := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.1.1
  have hA8mem : Work.Spaces.HkMem α 6 A8 := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.1.2
  have hA8mem4 : Work.Spaces.HkMem α 4 A8 :=
    Work.FTS.OpenPkg.HkMem_mono_open hA8sm 4 (by norm_num) hA8mem
  have hXn4 : Work.FTS.Nonlin.Xn α A4 ≤ Ce * Work.FTS.Nonlin.Xn α w := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.2
  have hXn8 : Work.FTS.Nonlin.Xn α A8 ≤ Ce * Work.FTS.Nonlin.Xn α w := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hell.V.2
  have hN4 : Work.Spaces.HkNorm α 6 A4 ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    rw [hA4def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.U.2
  have hN8 : Work.Spaces.HkNorm α 6 A8 ≤ Ce * Work.Spaces.HkNorm α 6 w := by
    rw [hA8def]; simpa only [Work.FTS.Nonlin.PhiTg] using hK6.V.2
  have hsq4 : Work.Spaces.HkSq α 6 A4 ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w :=
    hkSq_le_of_hkNorm_le 6 hN4
  have hsq8 : Work.Spaces.HkSq α 6 A8 ≤ Ce ^ 2 * Work.Spaces.HkSq α 6 w :=
    hkSq_le_of_hkNorm_le 6 hN8
  have hMA4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |A4 z θ| ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A4 := by
    intro z θ hz0 hθ hθ'
    have h := hsup α A4 hα0 hα1 hA4sm hA4mem4 0 (by norm_num) z θ hz0 hθ hθ'
    simpa using h
  have hMA8 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |A8 z θ| ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A8 := by
    intro z θ hz0 hθ hθ'
    have h := hsup α A8 hα0 hα1 hA8sm hA8mem4 0 (by norm_num) z θ hz0 hθ hθ'
    simpa using h
  have hKA8 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth A8 z θ| ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w := by
    intro z θ hz0 hθ hθ'
    have hmem : Work.FTS.VocabO.CoefThMem 1 A8 := by
      rw [hA8def]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.Vth.1
    have hbd : Work.FTS.VocabO.CoefTh 1 A8
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w := by
      rw [hA8def]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.Vth.2
    exact le_trans
      (Work.FTS.StrongPersist.H6Rows.abs_pth_le_coefTh hmem z θ hz0 hθ hθ') hbd
  -- ## the constant prices
  have hMAgen : ∀ B : ℝ → ℝ → ℝ, (Work.FTS.Nonlin.Xn α B) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 →
      (Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α B) ^ 2 ≤ KMA := by
    intro B hB
    have h2 : (Csup / Real.sqrt (Work.Spaces.gam α - 1)) ^ 2
        = Csup ^ 2 * (Work.Spaces.gam α - 1)⁻¹ := by
      rw [div_pow, Real.sq_sqrt hγ.le, div_eq_mul_inv]
    have h1 : (Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α B) ^ 2
        = (Csup / Real.sqrt (Work.Spaces.gam α - 1)) ^ 2 * (Work.FTS.Nonlin.Xn α B) ^ 2 :=
      mul_pow _ _ 2
    rw [h1, h2]
    refine le_trans (mul_le_mul_of_nonneg_left hB (mul_nonneg (sq_nonneg Csup) hGnn)) ?_
    rw [hKMAdef]
    have h7 : Csup ^ 2 * (Work.Spaces.gam α - 1)⁻¹ * (Ce ^ 2 * C₀ ^ 2)
        = (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 := by ring
    rw [h7]
    have hnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ * Csup ^ 2 * Ce ^ 2 * C₀ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hGnn (sq_nonneg Csup)) (sq_nonneg Ce)) (sq_nonneg C₀)
    linarith only [hnn]
  have hatom4 : (Work.FTS.Nonlin.Xn α A4) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α A4 ≤ |Ce| * Work.FTS.Nonlin.Xn α w := by
      refine le_trans hXn4 (le_trans (le_abs_self _) ?_)
      rw [abs_mul, abs_of_nonneg hXwnn]
    have h2 : (Work.FTS.Nonlin.Xn α A4) ^ 2 ≤ (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 :=
      sq_le_sq_of_nonneg (Real.sqrt_nonneg _) h1
    have h3 : (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
      rw [mul_pow, absSq_eq Ce]
      exact mul_le_mul_of_nonneg_left hwsq (sq_nonneg Ce)
    linarith only [h2, h3]
  have hatom8 : (Work.FTS.Nonlin.Xn α A8) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α A8 ≤ |Ce| * Work.FTS.Nonlin.Xn α w := by
      refine le_trans hXn8 (le_trans (le_abs_self _) ?_)
      rw [abs_mul, abs_of_nonneg hXwnn]
    have h2 : (Work.FTS.Nonlin.Xn α A8) ^ 2 ≤ (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 :=
      sq_le_sq_of_nonneg (Real.sqrt_nonneg _) h1
    have h3 : (|Ce| * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
      rw [mul_pow, absSq_eq Ce]
      exact mul_le_mul_of_nonneg_left hwsq (sq_nonneg Ce)
    linarith only [h2, h3]
  have hKA8sq : (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
    have hrw : α ^ (-(1 / 2 : ℝ)) * α ^ 2 = α ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα0]
      norm_num
    have hstep : α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w ≤ |C₀| * α ^ (3 / 2 : ℝ) := by
      calc α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w
          ≤ α ^ (-(1 / 2 : ℝ)) * (|C₀| * α ^ 2) :=
            mul_le_mul_of_nonneg_left hXw' (Real.rpow_nonneg hα0.le _)
        _ = |C₀| * (α ^ (-(1 / 2 : ℝ)) * α ^ 2) := by ring
        _ = |C₀| * α ^ (3 / 2 : ℝ) := by rw [hrw]
    have h1 : |Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w|
        ≤ |Ce| * (|C₀| * α ^ (3 / 2 : ℝ)) := by
      have hA : |Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w|
          = |Ce| * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hα0.le _),
          abs_of_nonneg hXwnn]
        ring
      rw [hA]
      exact mul_le_mul_of_nonneg_left hstep (abs_nonneg Ce)
    have h2 : (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2
        ≤ (|Ce| * (|C₀| * α ^ (3 / 2 : ℝ))) ^ 2 := by
      have h := sq_le_sq_of_nonneg (abs_nonneg _) h1
      rwa [absSq_eq] at h
    have h3 : (|Ce| * (|C₀| * α ^ (3 / 2 : ℝ))) ^ 2 ≤ Ce ^ 2 * C₀ ^ 2 := by
      have hα32 : (α ^ (3 / 2 : ℝ)) ^ 2 ≤ 1 := by
        have h5 : α ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα0.le hα1 (by norm_num)
        nlinarith only [h5, Real.rpow_nonneg hα0.le (3 / 2 : ℝ)]
      rw [mul_pow, mul_pow, absSq_eq Ce, absSq_eq C₀]
      have h4 : C₀ ^ 2 * (α ^ (3 / 2 : ℝ)) ^ 2 ≤ C₀ ^ 2 := by
        nlinarith only [hα32, sq_nonneg C₀]
      nlinarith only [h4, sq_nonneg Ce]
    linarith only [h2, h3]
  have hMA4sq := hMAgen A4 hatom4
  have hMA8sq := hMAgen A8 hatom8
  -- ## the bracket bounds
  have hE6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hE7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hA7 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith only [hE7]
  have hsum4 := sum_le_one_add hsq4 hE6 (sq_nonneg Ce)
  have hsum8 := sum_le_one_add hsq8 hE6 (sq_nonneg Ce)
  have hfac4 := one_add_mul_le hGnn hsum4 hE6 (sq_nonneg Ce)
  have hfac8 := one_add_mul_le hGnn hsum8 hE6 (sq_nonneg Ce)
  have hA40 : 0 ≤ Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 w := by
    have h := Work.Spaces.HkSq_nonneg α 6 A4; linarith only [h, hE6]
  have hA80 : 0 ≤ Work.Spaces.HkSq α 6 A8 + Work.Spaces.HkSq α 6 w := by
    have h := Work.Spaces.HkSq_nonneg α 6 A8; linarith only [h, hE6]
  have hbr4 := bracket_le hGnn hfac4 hsum4 hA40 hE6 (sq_nonneg Ce) hP34
  have hKA8b : 1 + (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2
      ≤ 1 + Ce ^ 2 * C₀ ^ 2 := by linarith only [hKA8sq]
  have hKA80 : (0 : ℝ)
      ≤ 1 + (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w) ^ 2 := by
    have := sq_nonneg (Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α w)
    linarith only [this]
  have hbr8 := bracket_le_KA hGnn hKA8b hfac8 hsum8 hA80 hE6 (sq_nonneg Ce) hKA80 hCeQ hP234
  -- ## the two product estimates
  have hbound4 : Work.Spaces.HkSq α 6 (fun z θ => A4 z θ * Work.Spaces.Dth w z θ)
      ≤ C4 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
          + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
    absorb_le hC4pos.le (mul_sq_le hMA4sq hE7 (by linarith only [hKMA1])) hbr4
      (h4 A4 w _ hA4sm hw.reg hA4mem h6w hw.mem hMA4)
  have hbound8 : Work.Spaces.HkSq α 6 (fun z θ => A8 z θ * Work.Spaces.Dz w z θ)
      ≤ C8 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
          + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
    absorb_le hC8pos.le (mul_sq_le hMA8sq hE7 (by linarith only [hKMA1])) hbr8
      (h8 A8 w _ _ hA8sm hw.reg hA8mem h6w hw.mem hMA8 hKA8)
  -- ## the two pieces
  constructor
  · have hself : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4
        = fun z θ => (-2 : ℝ) * (A4 z θ * Work.Spaces.Dth w z θ) := by
      funext z θ
      simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTg, hA4def]
    rw [hself, Work.FTS.StrongEps.HkSq_const_mul α 6 (-2)
      (fun z θ => A4 z θ * Work.Spaces.Dth w z θ)]
    calc (-2 : ℝ) ^ 2 * Work.Spaces.HkSq α 6 (fun z θ => A4 z θ * Work.Spaces.Dth w z θ)
        ≤ 4 * (C4 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
            + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2)) := by
          rw [show (-2 : ℝ) ^ 2 = 4 by norm_num]
          exact mul_le_mul_of_nonneg_left hbound4 (by norm_num)
      _ = (4 * C4 * KMA) * (1 + Work.Spaces.HkSq α 7 w)
          + (4 * C4 * KB) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by ring
      _ ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hK4KMA hA7)
            (mul_le_mul_of_nonneg_right hK4KB (sq_nonneg _))
  · have hself : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8
        = fun z θ => (-(2 * α)) * (A8 z θ * Work.Spaces.Dz w z θ) := by
      funext z θ
      simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTg, hA8def]
    rw [hself, Work.FTS.StrongEps.HkSq_const_mul α 6 (-(2 * α))
      (fun z θ => A8 z θ * Work.Spaces.Dz w z θ)]
    calc (-(2 * α)) ^ 2 * Work.Spaces.HkSq α 6 (fun z θ => A8 z θ * Work.Spaces.Dz w z θ)
        ≤ 4 * (C8 * (KMA * (1 + Work.Spaces.HkSq α 7 w)
            + KB * (1 + Work.Spaces.HkSq α 6 w) ^ 2)) :=
          mul_le_mul (by nlinarith only [hα0, hα1]) hbound8
            (Work.Spaces.HkSq_nonneg α 6 _) (by norm_num)
      _ = (4 * C8 * KMA) * (1 + Work.Spaces.HkSq α 7 w)
          + (4 * C8 * KB) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by ring
      _ ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hK8KMA hA7)
            (mul_le_mul_of_nonneg_right hK8KB (sq_nonneg _))

end Work.FTS.StrongEps.E4R3.Nblock6
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.P0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.P0` — the level-six bound of the single piece `NBlk 0`

`NBlk α w Φs Φg 0 = 2·(Rop α (PhiTg α w Φg)·w)`, i.e. a product `A·w` in which **both** factors
are `ℋ⁶`-priced (`HkNorm α 6 A ≤ Ce·HkNorm α 6 w` by `EllPkgK.R`, and `w` is honest to order 7 by
`ClassC`).  Unlike the pieces `4` and `8` (whose second factor `D_θw`/`D_zw` is a slot of order
one *above* the norm), no slot of order 7 occurs, so the crude level-six product rule
`N6.prod_field_of6` applies directly: with `α`-dependent constants (which the consumer `S2Stmt`
allows, since `Ct` is chosen after `α`) its `α^{-1/2}` loss is harmless and one gets
`HkSq α 6 (NBlk … 0) ≤ 4·(C·α^{-1/2}·Ce⁺·HkNorm α 6 w · HkNorm α 6 w)²`, i.e. the quadratic term.

This is a **fallback** for the `gg`-group: `Assembly.GGStmt_of_p0_p48` combines it with the
pieces `4, 8` (`N_b6_p48`) into `GGStmt`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem hkN_sq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    (Work.Spaces.HkNorm α k f) ^ 2 = Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkNorm]
  exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)

/-- The level-six bound of the piece `NBlk 0` (see `Stmts.P0Stmt`). -/
theorem N_b6_p0 : P0Stmt := by
  obtain ⟨Kmaj, hKmaj, hMaj⟩ := Work.FTS.StrongPersist.N6.prod_majorant6
  obtain ⟨Cexc, hCexc, hExc⟩ := Work.FTS.StrongPersist.N6.exc_bound6
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.StrongPersist.N6.prod_field_of6 ⟨Kmaj, hKmaj, hMaj⟩ ⟨Cexc, hCexc, hExc⟩
  intro C₀ Ce Cs α hα
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  refine ⟨4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1, by positivity, ?_⟩
  intro Φs w Φg hcls hXw hz hell hK hstar
  -- the honest `ℋ⁶`-data
  have hQoA : Work.FTS.VocabO.HQo α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) :=
    hK.R.1
  have hQow : Work.FTS.VocabO.HQo α 6 w :=
    ⟨hcls.reg, Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 6 (by norm_num) hcls.mem⟩
  have hCe0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hCell : Ce ≤ max Ce 0 := le_max_left Ce 0
  have hwnn : 0 ≤ Work.Spaces.HkNorm α 6 w := Work.Spaces.HkNorm_nonneg α 6 w
  have hA7nn : 0 ≤ 1 + Work.Spaces.HkSq α 7 w := by
    have := Work.Spaces.HkSq_nonneg α 7 w
    linarith
  -- the level-six product rule
  obtain ⟨-, hprod⟩ := hC α hα0 hα1
    (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) w hQoA hQow
  have hAnorm : Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg))
      ≤ max Ce 0 * Work.Spaces.HkNorm α 6 w :=
    le_trans hK.R.2 (mul_le_mul_of_nonneg_right hCell hwnn)
  have hCα : 0 ≤ C * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg hα0.le _)
  have hmain : Work.Spaces.HkNorm α 6 (fun z θ =>
        Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
      ≤ (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * (Work.Spaces.HkNorm α 6 w) ^ 2 := by
    refine le_trans hprod ?_
    calc C * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.HkNorm α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg))
          * Work.Spaces.HkNorm α 6 w
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0 * Work.Spaces.HkNorm α 6 w)
            * Work.Spaces.HkNorm α 6 w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAnorm hCα) hwnn
      _ = (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * (Work.Spaces.HkNorm α 6 w) ^ 2 := by ring
  -- transfer to `HkSq`
  have hbound : Work.Spaces.HkSq α 6 (fun z θ =>
        Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
      ≤ (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 * (Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h2 := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hmain 2
    calc Work.Spaces.HkSq α 6 (fun z θ =>
          Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
        = (Work.Spaces.HkNorm α 6 (fun z θ =>
            Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)) ^ 2 :=
          (hkN_sq α 6 _).symm
      _ ≤ ((C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * (Work.Spaces.HkNorm α 6 w) ^ 2) ^ 2 := h2
      _ = ((C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) * Work.Spaces.HkSq α 6 w) ^ 2 := by
          rw [hkN_sq α 6 w]
      _ = (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 * (Work.Spaces.HkSq α 6 w) ^ 2 := by
          ring
  -- the target
  have hNB : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0
      = fun z θ => 2 * (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ
          * w z θ) := rfl
  rw [hNB, Work.FTS.StrongEps.HkSq_const_mul]
  have h6w : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hsquare : (Work.Spaces.HkSq α 6 w) ^ 2 ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
    pow_le_pow_left₀ h6w (by linarith) 2
  have hcoef : 0 ≤ 4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 := by positivity
  have hfin : (2 : ℝ) ^ 2 * Work.Spaces.HkSq α 6 (fun z θ =>
        Work.Construction.Rop α (Work.Construction.PhiTil α w Φg) z θ * w z θ)
      ≤ (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1)
          * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsquare hcoef
    have h2 := mul_le_mul_of_nonneg_left hbound hcoef
    have hnn : 0 ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
    nlinarith [h2, h, hnn]
  have hfin2 : (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1)
        * (1 + Work.Spaces.HkSq α 6 w) ^ 2
      ≤ (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w)
        + (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1)
          * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h : 0 ≤ (4 * (C * α ^ (-(1 / 2 : ℝ)) * (max Ce 0)) ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w) :=
      mul_nonneg (by positivity) hA7nn
    linarith
  exact le_trans hfin hfin2

end Work.FTS.StrongEps.E4R3.Nblock6
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.Base =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Extraction from `ClassC` -/

/-- `ClassC` gives `SmoothOpen`. -/
theorem cSmooth {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.EllipticEst.SmoothOpen W := hW.reg

/-- From `ClassC` (`HkMem α 7`) to any order `≤ 7`. -/
theorem cMem {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) {k : ℕ} (hk : k ≤ 7) :
    Work.Spaces.HkMem α k W :=
  Work.FTS.OpenPkg.HkMem_mono_open hW.reg k hk hW.mem

/-- `ClassC` gives `HQo α 4`. -/
theorem cHQo {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.VocabO.HQo α 4 W :=
  ⟨hW.reg, cMem hW (by norm_num)⟩


/-! ## The difference of two class elements -/

/-- The difference of two class-`C` elements is again of class `C`. -/
theorem sub_classC {α : ℝ} {W₁ W₂ : Fn}
    (h₁ : Work.FTS.ClassC.ClassC α W₁) (h₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
  Work.FTS.StrongEps.EComparison.classC_sub h₁ h₂

/-- `L₁₂` of a difference of two class-`C` elements at `z = 0` vanishes: additivity of `L₁₂`
(`Sharp.L12_sub_ge0`, at `z = 0`) plus the class field `L12 W 0 = 0`. -/
theorem sub_L12_zero {α : ℝ} {W₁ W₂ : Fn}
    (h₁ : Work.FTS.ClassC.ClassC α W₁) (h₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) 0 = 0 := by
  have hd := sub_classC h₁ h₂
  have hsub := Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0 (d := fun z θ => W₁ z θ - W₂ z θ)
    h₁.reg h₂.reg hd.reg (cMem h₁ (by norm_num)) (cMem h₂ (by norm_num))
    (cMem hd (by norm_num)) (fun z θ => rfl) (le_refl 0)
  rw [h₁.l12, h₂.l12] at hsub
  linarith [hsub]


end Work.FTS.StrongEps.EpsRLX.CCSharp
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The `ℋ⁴`-slot bound for the transfer profile `radA`

The two facts about the transfer profile that the sharp bound of `𝓛_Γ^T` on the class `C`
consumes.  `L12fSlotLe` is the `L₁₂`-side slot estimate (a corollary of
`Work.FTS.OpenPkg.l12H_field` + `Work.Elliptic.HkSq_rad`), and `radA_slot5_le_classC_of` is the
`radA`-side one, whose proof needs the Leibniz expansion of `radA α f = −ampA α·L₁₂f +
(ampB α/c)·L₁₂(Transport f)(0)` together with the uniform boundedness of the `D_z`-iterates of
`ampA`, `ampB/c` and of the constant `L₁₂(Transport f)(0)`. -/


/-- **(transfer-slot estimate, order 4.)**  The `radA`-side of the transfer slot bound, derived
from `L12SlotHyp`. -/
def RadASlotHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 →
    MeasureTheory.IntegrableOn (fun z : ℝ =>
        Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, Work.FTS.GalFields.Norm.slot5
        (Work.FTS.CoercivityFix.Transfer.radA α f) z) ≤ C * Work.Spaces.HkSq α 4 f

/-! ## The sharp `ℋ⁴`-bound of `𝓛_Γ^T` on the class `C`

`𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`).  The clean part is
`HkSq_Lhat_le_uniform`, and the transfer defect `Corr α h = Γ(θ)·radA α h z` is handled by the
separated pointwise majorant `HkIntegrand_Corr_le` (`HkSq_Corr_le_classC`) together with the
radial slot bound `RadASlotHyp`. -/

private theorem lgtProfile (hrad : RadASlotHyp) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {h : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α h →
      Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α h) ≤ K * Work.Spaces.HkSq α 5 h := by
  obtain ⟨Cl, hClpos, hL⟩ := Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform
  obtain ⟨Kang, hKangpos, hang⟩ := Work.FTS.GalFields.Norm.ang_fac_integrable_bound
  obtain ⟨Crad, hCradpos, hradspec⟩ := hrad
  refine ⟨2 * Cl + 2 * (Kang * Crad) + 1, by positivity, ?_⟩
  intro α hαIoc h hC
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have h5 : Work.Spaces.HkMem α 5 h :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 5 (by norm_num) hC.mem
  have h4 : Work.Spaces.HkMem α 4 h :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 4 (by norm_num) hC.mem
  -- ## the clean part `𝓛̂ h`
  have hLhat_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat h) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hC.reg h5
  have hLhat_bd : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h)
      ≤ Cl * Work.Spaces.HkSq α 5 h := hL α hα h hC.reg h5
  have hLhat_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Lhat h))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hC.reg).forall 4
  -- ## the transfer defect `Corr α h`
  have hCorr_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α h) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hC
  have hCorr_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α h))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hC.reg h5).2
  obtain ⟨hslot_int, hslot_bd⟩ := hradspec α hαIoc h hC.reg h4 hC.l12
  have hCorr_bd : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α h)
      ≤ Kang * (Crad * Work.Spaces.HkSq α 4 h) :=
    (Work.FTS.StrongEps.ClassCRHS.HkSq_Corr_le_classC hα hα1 hKangpos
      (hang α hα hα1) hslot_int).trans (mul_le_mul_of_nonneg_left hslot_bd hKangpos.le)
  -- ## the sum
  have hLGT_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat h
      + Work.FTS.CoercivityFix.Corr α h) :=
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hLhat_sm hCorr_sm hLhat_mem hCorr_mem
  have hpt_add : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Lhat h
          + Work.FTS.CoercivityFix.Corr α h) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Lhat h) z θ
          + 2 * Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α h) z θ :=
    fun z hz θ hθ =>
      Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 4
        (f := Work.FTS.CoercivityFix.Lhat h) (g := Work.FTS.CoercivityFix.Corr α h)
        hLhat_sm hCorr_sm z hz θ hθ
  have hsum : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h
        + Work.FTS.CoercivityFix.Corr α h)
      ≤ 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h)
        + 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α h) :=
    Work.FTS.CoercivityFix.Transfer.E2norm.HkSq_add_le α 4 hLhat_mem hCorr_mem hLGT_mem hpt_add
  have hmono : Work.Spaces.HkSq α 4 h ≤ Work.Spaces.HkSq α 5 h :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h5
  have h5nn : 0 ≤ Work.Spaces.HkSq α 5 h := Work.Spaces.HkSq_nonneg α 5 h
  have hstep : 2 * (Cl * Work.Spaces.HkSq α 5 h) + 2 * (Kang * (Crad * Work.Spaces.HkSq α 4 h))
      ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := by
    have hKC : 0 ≤ 2 * (Kang * Crad) := by positivity
    calc 2 * (Cl * Work.Spaces.HkSq α 5 h) + 2 * (Kang * (Crad * Work.Spaces.HkSq α 4 h))
        = (2 * Cl) * Work.Spaces.HkSq α 5 h
          + (2 * (Kang * Crad)) * Work.Spaces.HkSq α 4 h := by ring
      _ ≤ (2 * Cl) * Work.Spaces.HkSq α 5 h
          + (2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmono hKC)
      _ = (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := by ring
  have hmain : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α h)
      ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α h]
    calc Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h
            + Work.FTS.CoercivityFix.Corr α h)
        ≤ 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat h)
          + 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α h) := hsum
      _ ≤ 2 * (Cl * Work.Spaces.HkSq α 5 h) + 2 * (Kang * (Crad * Work.Spaces.HkSq α 4 h)) :=
          add_le_add (mul_le_mul_of_nonneg_left hLhat_bd (by norm_num))
            (mul_le_mul_of_nonneg_left hCorr_bd (by norm_num))
      _ ≤ (2 * Cl + 2 * (Kang * Crad)) * Work.Spaces.HkSq α 5 h := hstep
  exact hmain.trans (mul_le_mul_of_nonneg_right (by linarith) h5nn)

/-! ## The difference statement

`𝓛_Γ^T` is linear on the open quadrant (`sharp_LGammaT_diff_eqOn`), so the difference of the two
values is `𝓛_Γ^T` of the difference, and all three clauses transfer along the pointwise identity
(`smoothOpen_of_eqOn`-style congruence, `HkMem_congr_Q0`, `HkSq_congr_open`). -/

private theorem lgtDiff_assembly (hrad : RadASlotHyp) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
        ≤ K * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨Kp, hKppos, hprof⟩ := lgtProfile hrad
  refine ⟨Real.sqrt Kp + 1, by positivity, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  have h4₁ : Work.Spaces.HkMem α 4 W₁ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₁.reg 4 (by norm_num) hW₁.mem
  have h4₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 4 (by norm_num) hW₂.mem
  -- the pointwise identity on the open quadrant
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ
        = Work.Coercivity.LGammaT α (fun z θ => W₁ z θ - W₂ z θ) z θ :=
    fun z θ hz hθ0 hθ1 =>
      Work.FTS.GalFields.RHS.sharp_LGammaT_diff_eqOn hα hα1 hW₁.reg hW₂.reg h4₁ h4₂
        z θ hz hθ0 hθ1
  have hhC : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.StrongEps.EComparison.classC_sub hW₁ hW₂
  -- the two `𝓛_Γ^T Wᵢ` are `C^∞` on the open quadrant
  have hsm₁ : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α W₁) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hW₁) hW₁.reg
  have hsm₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α W₂) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hW₂) hW₂.reg
  -- the `ℋ⁴`-honesty of `𝓛_Γ^T (W₁ − W₂)`
  have h5h : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hhC.reg 5 (by norm_num) hhC.mem
  have hLhat_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Lhat
      (fun z θ => W₁ z θ - W₂ z θ))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hhC.reg).forall 4
  have hCorr_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α
      (fun z θ => W₁ z θ - W₂ z θ))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hhC.reg h5h).2
  have hLhat_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat
      (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hhC.reg h5h
  have hCorr_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α
      (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.HkMem_Corr_of_classC hα hα1 hhC
  have hmemh : Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α
      (fun z θ => W₁ z θ - W₂ z θ)) := by
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α (fun z θ => W₁ z θ - W₂ z θ)]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hLhat_sm hCorr_sm hLhat_mem hCorr_mem
  -- the sharp profile bound for the difference
  have hb : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
      (fun z θ => W₁ z θ - W₂ z θ)) ≤ Kp * Work.Spaces.HkSq α 5
        (fun z θ => W₁ z θ - W₂ z θ) := hprof hαIoc hhC
  have hsq : Work.Spaces.HkSq α 4 (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
      = Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
        (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => hid z θ hz hθ0 hθ1)
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: open-quadrant smoothness
    exact Work.FTS.NonlinRows.smoothOpen_sub hsm₁ hsm₂
  · -- conjunct 2: `ℋ⁴`-honesty, transported along the identity
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmemh
      (fun z hz θ hθ => (hid z θ hz hθ.1 hθ.2).symm)
  · -- conjunct 3: the `Xn`-bound
    have hKpnn : 0 ≤ Kp := hKppos.le
    have h5nn : 0 ≤ Work.Spaces.HkSq α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
      Work.Spaces.HkSq_nonneg α 5 _
    have hXnb : Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α
          (fun z θ => W₁ z θ - W₂ z θ)) ≤ Real.sqrt Kp * Work.FTS.GalFields.Xn5 α
            (fun z θ => W₁ z θ - W₂ z θ) := by
      show Real.sqrt (Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
            (fun z θ => W₁ z θ - W₂ z θ)))
          ≤ Real.sqrt Kp * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
      calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α
              (fun z θ => W₁ z θ - W₂ z θ)))
          ≤ Real.sqrt (Kp * Work.Spaces.HkSq α 5 (fun z θ => W₁ z θ - W₂ z θ)) :=
            Real.sqrt_le_sqrt hb
        _ = Real.sqrt Kp * Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => W₁ z θ - W₂ z θ)) :=
            Real.sqrt_mul hKpnn _
        _ = Real.sqrt Kp * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := rfl
    have hXnEq : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
        = Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α
          (fun z θ => W₁ z θ - W₂ z θ)) := by
      show Real.sqrt (Work.Spaces.HkSq α 4 _) = Real.sqrt (Work.Spaces.HkSq α 4 _)
      rw [hsq]
    rw [hXnEq]
    calc Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α (fun z θ => W₁ z θ - W₂ z θ))
        ≤ Real.sqrt Kp * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := hXnb
      _ ≤ (Real.sqrt Kp + 1) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          have h0 : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
            Work.Spaces.HkNorm_nonneg α 5 _
          linarith [mul_nonneg (Real.sqrt_nonneg Kp) h0]

theorem LGTDiffClassC {α : ℝ} (hα : α ∈ Set.Ioc 0 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)
        ≤ K * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
  lgtDiff_assembly (RadBound.radA_slot5_le_classC_of RadBound.L12fSlotLe) hα

end Work.FTS.StrongEps.EpsRLX
end
