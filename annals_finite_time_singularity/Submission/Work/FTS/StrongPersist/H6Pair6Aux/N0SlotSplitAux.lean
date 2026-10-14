import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingSplit
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyA
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst (SmoothOpen)

/-! ## Congruence of the mixed slots and of `HkMem` on the open quadrant

`Work.Construction.Qd = (0,∞) × (0,π/2)` is co-null in the integration domain
`Iz × Iθ = [0,∞) × [0,π/2]`, and the mixed operators `D_z^bD_θ^a` are local, so two
functions that agree on `Qd` have the same `Hk`-integrand almost everywhere.  These two
lemmas let us replace a piece by any pointwise-equal (on `Qd`) expression without any
integrability bookkeeping. -/

/-- **`D_z^bD_θ^a` is local on the open quadrant**: functions that agree on `Qd` have the
same mixed slots there. -/
theorem mixed_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j i, Work.Spaces.mixed j i f z θ
      = Work.Spaces.mixed j i f' z θ := by
  have hDth : ∀ i, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DthIter i f z θ = Work.Spaces.DthIter i f' z θ := by
    intro i
    induction i with
    | zero =>
        intro z θ hzθ
        exact h z θ hzθ
    | succ i ih =>
        intro z θ hzθ
        have hh : Work.Spaces.Dth (Work.Spaces.DthIter i f) z θ
            = Work.Spaces.Dth (Work.Spaces.DthIter i f') z θ :=
          Work.FTS.CoercivityStep.Base.Dth_congr_Qd ih z θ hzθ
        simpa only [Work.Spaces.DthIter_succ] using hh
  have hDz : ∀ j (X Y : ℝ → ℝ → ℝ),
      (∀ z θ, (z, θ) ∈ Work.Construction.Qd → X z θ = Y z θ) →
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.DzIter j X z θ = Work.Spaces.DzIter j Y z θ := by
    intro j
    induction j with
    | zero =>
        intro X Y hXY z θ hzθ
        exact hXY z θ hzθ
    | succ j ih =>
        intro X Y hXY z θ hzθ
        have hh : Work.Spaces.Dz (Work.Spaces.DzIter j X) z θ
            = Work.Spaces.Dz (Work.Spaces.DzIter j Y) z θ :=
          Work.FTS.CoercivityStep.Base.Dz_congr_Qd (ih X Y hXY) z θ hzθ
        simpa only [Work.Spaces.DzIter_succ] using hh
  intro z θ hzθ j i
  exact hDz j (Work.Spaces.DthIter i f) (Work.Spaces.DthIter i f') (hDth i) z θ hzθ

/-- **The `H^k`-integrand is local on the open quadrant.** -/
theorem HkIntegrand_congr_Qd {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k f' z θ := by
  have hDz : ∀ j, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.DzIter j f z θ = Work.Spaces.DzIter j f' z θ := by
    intro j
    induction j with
    | zero =>
        intro z θ hzθ
        exact h z θ hzθ
    | succ j ih =>
        intro z θ hzθ
        have hh : Work.Spaces.Dz (Work.Spaces.DzIter j f) z θ
            = Work.Spaces.Dz (Work.Spaces.DzIter j f') z θ :=
          Work.FTS.CoercivityStep.Base.Dz_congr_Qd ih z θ hzθ
        simpa only [Work.Spaces.DzIter_succ] using hh
  intro z θ hzθ
  have hmx := mixed_congr_Qd h z θ hzθ
  simp only [Work.Spaces.HkIntegrand]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [hDz i z θ hzθ]
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      split_ifs with hc
      · rw [hmx j i]
      · rfl

/-- **`HkMem` is local on the open quadrant.** -/
theorem HkMem_congr_Qd {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ)
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k f' := by
  have hae : ∀ z : ℝ, 0 ≤ z →
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.HkIntegrand α k f' z θ) := by
    intro z hz
    rcases eq_or_lt_of_le hz with h0 | hpos
    · have hz0 : z = 0 := h0.symm
      subst hz0
      have h1 : (fun θ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α k f θ
      have h2 : (fun θ => Work.Spaces.HkIntegrand α k f' 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α k f' θ
      rw [h1, h2]
    · have hset : volume.restrict Work.Spaces.Iθ
          = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
      rw [hset]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => HkIntegrand_congr_Qd h z θ ⟨hpos, hθ⟩)
  constructor
  · intro z hz
    exact (hf.1 z hz).congr (hae z (show (0 : ℝ) ≤ z from hz))
  · refine hf.2.congr ?_
    have hres : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
      (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
    rw [hres]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact integral_congr_ae (hae z (le_of_lt hz))

/-! ## Congruence of the slot pairing on the open quadrant -/

/-- **The slot pairing only sees the values on the open quadrant.** -/
theorem slotPairing_congr_Qd {ρ : ℝ → ℝ → ℝ} {a b : ℕ} {u u' v : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → u z θ = u' z θ) :
    Work.FTS.TransportS.slotPairing ρ a b u v = Work.FTS.TransportS.slotPairing ρ a b u' v := by
  rw [slotPairing_eq_wip ρ a b u v, slotPairing_eq_wip ρ a b u' v]
  exact Work.FTS.CoercivityStep.Base.wip_congr_Qd
    (fun z θ hzθ => mixed_congr_Qd h z θ hzθ b a)

/-! ## The `𝒲^{6,∞}`-priced product rule at level six, for all `α ∈ (0,1]`

`Work.FTS.StrongPersist.H6Rows.wprod6` carries an existential `α₂` in its conclusion (the
level-six rows of the modulation carry that constant in their own statements).  The
statement proved here has no such restriction: its proof is the assembly of `wprod6`
(`wprod6_of_slots`) with the three slot lemmas `zslot_le_winf6`, `dzIter_w_mean_le6`,
`mslot_le_winf6`, which are all stated for `α ≤ 1`. -/

/-- **Product rule**: the product of a `𝒲^{6,∞}`-function and an `ℋ⁶`-function is honest. -/
theorem HkMem_mul_of_WlInf6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} (hfs : SmoothOpen f) (hfw : Work.Spaces.WlInfMem α 6 f)
    (hgs : SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g) :
    Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) := by
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6
  obtain ⟨CB, hCB, hMe⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6
  obtain ⟨Cm, hCm, hMx⟩ := Work.FTS.StrongPersist.H6Rows.wprod6.mslot_le_winf6 CB
  set K : ℝ := 7 * Cz + 49 * Cm with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hfgsm : SmoothOpen (fun z θ => f z θ * g z θ) := hfs.mul hgs
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro z hz θ hθ
    rw [hKdef]
    exact Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6 hα hα1 hfs hfw hgs hgm
      hCz hCm
      (fun i hi z' θ' hz' hθ1 hθ2 => hZ α f g hα hα1 hfs hfw hgs i hi z' θ' hz' hθ1 hθ2)
      (fun I J hI hIJ z' θ' hz' hθ1 hθ2 =>
        hMx α f g hα hα1 hfs hfw hgs hgm
          (fun d hd z'' θ'' hz'' hθ1' hθ2' =>
            hMe α g d hα hα1 hgs hgm hd z'' θ'' hz'' hθ1' hθ2')
          I J hI hIJ z' θ' hz' hθ1 hθ2)
      z hz θ hθ
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6
      (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul
          (K * (Work.Spaces.WlInf α 6 f) ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 6) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)]
        exact hmajor z hz θ hθ
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2
            * (1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹)))
          * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 6 f) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            (K * (Work.Spaces.WlInf α 6 f) ^ 2)
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
        ≤ (1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹))
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      simpa only [Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := g)
          hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
                Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * ((1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹))
              * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
      _ = (K * (Work.Spaces.WlInf α 6 f) ^ 2
            * (1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹)))
          * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 6 f) ^ 2
      * (1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹)))
        * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) Work.Spaces.Iz :=
    hgm.2.const_mul _
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 6)).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)]
    exact hbdd z hz
  exact ⟨hslice, hzg⟩

/-! ## Splitting a slot pairing over seven summands -/



end Work.FTS.StrongPersist.H6Pair6Aux
