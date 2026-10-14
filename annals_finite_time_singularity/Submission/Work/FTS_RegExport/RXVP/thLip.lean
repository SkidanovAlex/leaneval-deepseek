import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.E5Aux2.FK_JfamP_tendsto
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsWPBounds
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.gRHS_tendsto
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T3Honest
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.cs7_theta_holder
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `MuHGlue` — measurability and domination glue for the `μ`-convergence

Three general facts used in `muDyn_tendstoH`:

* `aesm_L12dens_of_contOn` — joint continuity of a profile on the open quadrant gives
  a.e.-strong measurability of its `L₁₂`-density;
* `aesm_slice_K_of_contOn` — the same continuity gives the a.e.-strong measurability of the
  angular slice `θ ↦ K θ · Y s θ` at every `s > 0`;
* `integrable_majorant` — the majorant
  `s ↦ C1 (1+C₀) (1+B) (Maj s / s + 1/(1+s)²)` is integrable on `(0,∞)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-! ## Measurability of the density from joint continuity on the open quadrant -/

/-- The uncurried profile is a.e.-strongly measurable for the product of the restrictions of
Lebesgue measure to `(0,∞)` and to `Iθ`, from joint continuity on the open quadrant. -/
theorem aesm_uncurry_of_contOn {Y : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry Y) h
  have hle : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl) le_rfl
  exact h1.mono_measure hle

/-- **The `L₁₂`-density of a profile that is continuous on the open quadrant is
a.e.-strongly measurable.**  The `θ`-integral is taken against the restricted product measure
of the (a.e. equal) sets `(0,∞) × Iθ` and the open quadrant. -/
theorem aesm_L12dens_of_contOn {Y : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable (fun s => Work.FM.L12dens Work.Spaces.K Y s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aestronglyMeasurable_L12dens (aesm_uncurry_of_contOn h).aemeasurable

/-- The angular slice `θ ↦ K θ · Y s θ` is a.e.-strongly measurable on `Iθ` for every `s > 0`,
from joint continuity of `Y` on the open quadrant (the slice is continuous on `(0,π/2)`, which
is co-null in `Iθ`). -/
theorem aesm_slice_K_of_contOn {Y : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Y s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hslice : ContinuousOn (fun θ => Y s θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    h.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hs, hθ⟩)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    unfold Work.Spaces.K
    fun_prop
  have h2 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.K θ * Y s θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hK.mul hslice).aestronglyMeasurable measurableSet_Ioo
  have hcongr : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))
  rwa [hcongr] at h2

/-! ## Integrability of the majorant -/

/-- `s ↦ 1/(1+s)²` is integrable on `(0,∞)`. -/
theorem integrableOn_one_div_sq : MeasureTheory.IntegrableOn
    (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    (MeasureTheory.Integrable.const_mul
      (Work.FTS.MeridianDyn.Bridge.Pieces.integrableOn_two_div_one_add_sq 0 le_rfl)
      (1 / 2)) ?_ measurableSet_Ioi
  intro s _
  ring

/-- **The majorant of the `ε`-density bound is integrable on `(0,∞)`**, from the integrability
of `Maj s / s`. -/
theorem integrable_majorant {C1 C₀ B : ℝ} {Maj : ℝ → ℝ}
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => C1 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2))
      (Set.Ioi 0) :=
  ((hMajint.add integrableOn_one_div_sq).const_mul _)

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ConjOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem ConjOne {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ) (u : Fn),
      Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.Spaces.HkNorm α 6 u ≤ B →
      Work.FTS.ClassC.ClassC α (Wp ρ ε u) → Work.FTS.Nonlin.Xn α (Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ≤ L := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα.1
    linarith
  -- ## the uniform enlargement of the size parameter
  obtain ⟨CW, hCWpos, hCW⟩ := WpSixBound (ρ := ρ) hρ
  set BS : ℝ := max B (CW / (Work.Spaces.gam α - 1) * (CW / ε) ^ 6 * B) with hBSdef
  have hBS0 : 0 ≤ BS := le_trans hB (by rw [hBSdef]; exact le_max_left _ _)
  have hWp6 : ∀ {u : Fn}, ProfileData α C₀ B ε ρ u → Work.Spaces.HkNorm α 6 (Wp ρ ε u) ≤ BS :=
    fun hd => le_trans (hCW α hα ε ⟨hε, hε1⟩ hB hd) (by
      rw [hBSdef]; exact le_max_right _ _)
  -- ## the data of the pre-mollified right-hand side, at the enlarged size
  obtain ⟨R, hRpos, hRdata⟩ := XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := BS)
    hα hEll hstar hml hBS0
  obtain ⟨R₂, hR₂pos, hR₂⟩ := ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (B := BS)
    hα hEll hstar hml hBS0
  obtain ⟨CP, hCPpos, hCP⟩ := EpsSq_Pz_le
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le ρ hρ
  obtain ⟨CM, -, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  refine ⟨max 1 (CP * CJ * R₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ u hu hmu hnu hclu hxnu
  set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
  set Φ : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hΦdef
  have hclu' : Work.FTS.ClassC.ClassC α W := hclu
  have hxnu' : Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 := hxnu
  have hW6 : Work.Spaces.HkNorm α 6 W ≤ BS := hWp6 (u := u) ⟨hu, hmu, hnu, hclu, hxnu⟩
  -- the pre-mollified right-hand side at `W`
  obtain ⟨hXsm, hXmem, -⟩ := hRdata (W := W) hclu' hxnu' hW6
  obtain ⟨hXepsMem, hXepsSq⟩ := hR₂ (W := W) hclu' hxnu' hW6
  -- the mollified profile
  have hsmΦ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hXsm
  have hJsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmΦ
  have hJmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmΦ hXmem
  have hJepsMem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    (hCM α hα ε hε hε1 Φ hsmΦ hXepsMem).1
  have hJepsSq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ)
      ≤ CJ * Work.FTS.StrongEps.EpsSq α Φ := by
    have h := hCJ α hα ε ⟨hε, hε1⟩ Φ hsmΦ hXepsMem 0 0 (by norm_num)
    have h1 : Work.FTS.StrongEps.EpsSq α
        (Work.Spaces.mixed 0 0 (Work.FTS.StrongEps.Jeps ρ ε Φ))
        = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    have h2 : CJ * (CJ / ε) ^ (2 * (0 + 0)) * Work.FTS.StrongEps.EpsSq α Φ
        = CJ * Work.FTS.StrongEps.EpsSq α Φ := by norm_num
    rw [h1, h2] at h
    exact h
  obtain ⟨hPzMem, hPzSq⟩ := hCP α hα (Work.FTS.StrongEps.Jeps ρ ε Φ) hJsm hJmem hJepsMem
  have hslice : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
    rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS]
  refine ⟨?_, ?_⟩
  · rw [hslice]; exact hPzMem
  · rw [hslice]
    calc Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ))
        ≤ CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := hPzSq
      _ ≤ CP * (CJ * Work.FTS.StrongEps.EpsSq α Φ) :=
          mul_le_mul_of_nonneg_left hJepsSq hCPpos.le
      _ = CP * CJ * Work.FTS.StrongEps.EpsSq α Φ := by ring
      _ ≤ CP * CJ * R₂ := mul_le_mul_of_nonneg_left hXepsSq (mul_nonneg hCPpos.le hCJpos.le)
      _ ≤ max 1 (CP * CJ * R₂) := le_max_right _ _

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_sup_le_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.FTS.StrongEps

/-- The family version of `epsWP_abs_le_on_compact`: the same explicit bound, uniform in `n`. -/
theorem epsWP_abs_le_on_compact_fam {α C₀ B T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hB : 0 ≤ B)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ|
        + |Work.Spaces.pth (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.Spaces.Dz (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ|
        + |Work.Spaces.Dz (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ|
        + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ|
        + |Work.Construction.AK α z θ| ≤ B)
    (hcoef : ∀ z θ : ℝ, (z, θ) ∈ K →
      |2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)| ≤ B)
    (hcoef2 : ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3)| ≤ B)
    (hL12f : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B)
    (hL12T : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Coercivity.L12f (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0| ≤ B)
    (hL12F : ∀ z ∈ Work.Spaces.Iz, |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hFK : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B)
    (hmubar : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
        (Work.Construction.N α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))| ≤ B) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s z θ| ≤ B' := by
  obtain ⟨hα0, hα1⟩ := hα
  refine ⟨1 + (28 * B + 32 * B ^ 2)
      + ((B + 1) ^ 2 + (4 / α + 6) * (B + 1) ^ 2 + 8 * (B + 1) ^ 2 + 3 * (B + 1)), ?_, ?_⟩
  · have h4a : (0 : ℝ) < 4 / α := by positivity
    have hB1 : (0 : ℝ) < B + 1 := by linarith
    have hB1sq : (0 : ℝ) < (B + 1) ^ 2 := by positivity
    have hprod : (0 : ℝ) < (4 / α + 6) * (B + 1) ^ 2 := by positivity
    have h8 : (0 : ℝ) ≤ 8 * (B + 1) ^ 2 := by positivity
    have h28 : (0 : ℝ) ≤ 28 * B := by linarith
    have h32 : (0 : ℝ) ≤ 32 * B ^ 2 := by positivity
    have h3 : (0 : ℝ) < 3 * (B + 1) := by linarith
    linarith
  · intro n s hs z θ hzθ
    rw [show Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s z θ
        = -(Work.Coercivity.LGammaT α
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.FTS.Galerkin.lamDyn α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ from rfl]
    set J : Work.FTS.Galerkin.Fam := Work.FTS.StrongEps.JfamP ρ (ε n) (G n) with hJ
    set Φ : Work.FTS.Galerkin.Fam := Work.FTS.Nonlin.PsiCan Φs E J with hΦdef
    set f : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice J s with hfs
    set F : Work.FTS.Galerkin.Fn := Work.Construction.Ftau α J s with hFdef
    set Φs' : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice Φ s with hΦsdef
    -- the point of `K`
    have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hKQ hzθ
    obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    have hzge : (0 : ℝ) ≤ z := le_of_lt hzpos
    have hzIz : z ∈ Work.Spaces.Iz := hzge
    have hb := hbnd n s hs z θ hzθ
    -- the individual bounds extracted from the eleven-term sum
    have ha1 : (0 : ℝ) ≤ |F z θ| := abs_nonneg _
    have ha2 : (0 : ℝ) ≤ |Work.Spaces.pth F z θ| := abs_nonneg _
    have ha3 : (0 : ℝ) ≤ |Work.Spaces.Dz F z θ| := abs_nonneg _
    have ha4 : (0 : ℝ) ≤ |f z θ| := abs_nonneg _
    have ha5 : (0 : ℝ) ≤ |Work.Spaces.Dz f z θ| := abs_nonneg _
    have ha6 : (0 : ℝ) ≤ |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := abs_nonneg _
    have ha7 : (0 : ℝ) ≤ |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := abs_nonneg _
    have ha8 : (0 : ℝ) ≤ |Work.Construction.Rop α (Work.Construction.PhiTil α F Φs') z θ| :=
      abs_nonneg _
    have ha9 : (0 : ℝ) ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α F Φs') z θ| :=
      abs_nonneg _
    have ha10 : (0 : ℝ) ≤ |Work.Construction.Vop (Work.Construction.PhiTil α F Φs') z θ| :=
      abs_nonneg _
    have ha11 : (0 : ℝ) ≤ |Work.Construction.AK α z θ| := abs_nonneg _
    have ht2 : |Work.Spaces.pth F z θ| ≤ B := by
      linarith [hb, ha1, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]
    have ht4 : |f z θ| ≤ B := by
      linarith [hb, ha1, ha2, ha3, ha5, ha6, ha7, ha8, ha9, ha10, ha11]
    have ht5 : |Work.Spaces.Dz f z θ| ≤ B := by
      linarith [hb, ha1, ha2, ha3, ha4, ha6, ha7, ha8, ha9, ha10, ha11]
    have ht6 : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ B := by
      linarith [hb, ha1, ha2, ha3, ha4, ha5, ha7, ha8, ha9, ha10, ha11]
    -- the `D_θ`-bound on the slice: `pth (F_*+f) = pth F_* + pth f`
    have hdth : |Work.Spaces.Dth f z θ| ≤ 2 * B := by
      have h := Work.FTS.StrongEps.EpsWp.Dth_slice_le (α := α) (G := J) (s := s)
        (hC n s hs).reg hzpos hθ0 hθ1
      linarith [h, ht2, ht6]
    -- the linear part `𝓛_Γ^T`
    have hLG : |Work.Coercivity.LGammaT α f z θ| ≤ 28 * B + 32 * B ^ 2 := by
      have h4B : (0 : ℝ) ≤ 4 * B := by linarith
      have key : |Work.Coercivity.LGammaT α f z θ| ≤ 7 * (4 * B) + 2 * ((4 * B) * (4 * B)) :=
        Work.FTS.StrongEps.EpsWp.LGammaT_abs_le_explicit (α := α) (B := 4 * B) (f := f) h4B hzge
          (by linarith [ht4, ht5, hdth])
          (by linarith [hcoef z θ hzθ])
          (by linarith [hcoef2 z θ hzθ])
          (by have h := hL12f n s hs z hzIz
              have h' : |Work.Coercivity.L12f f z| ≤ B := h
              linarith)
          (by have h := hL12T n s hs
              have h' : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ B := h
              linarith)
      convert key using 1
      ring
    -- the modulation constants, from `MuLamOK` at the slice-constant family
    have hμ : |Work.FTS.Galerkin.muDyn α Φ J s| ≤ 1 / 2 := by
      have h := (hml f (hC n s hs) (hb4 n s hs)).1
      rw [show Work.FTS.Galerkin.muDyn α Φ J s
          = Work.FTS.Galerkin.muDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
          from rfl]
      exact h
    have hlam : |Work.FTS.Galerkin.lamDyn α Φ J s| ≤ 1 := by
      have h := (hml f (hC n s hs) (hb4 n s hs)).2
      rw [show Work.FTS.Galerkin.lamDyn α Φ J s
          = Work.FTS.Galerkin.lamDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
          from rfl]
      exact h
    -- the nonlinear part `gRHS`, with the common bound `B + 1`
    have hGR : |Work.Construction.gRHS α
        (Work.FTS.Galerkin.muDyn α Φ J s) (Work.FTS.Galerkin.lamDyn α Φ J s)
        F Φs' f z θ|
        ≤ (B + 1) ^ 2 + (4 / α + 6) * (B + 1) ^ 2 + 8 * (B + 1) ^ 2 + 3 * (B + 1) := by
      have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
      have hfk : |Work.Construction.FK F z| ≤ B + 1 :=
        Work.FTS.StrongEps.EpsWp.FK_fstar_add_bound (α := α) (f := f) (B := B) hα0 hα1 hB
          (by intro z' hz'; rw [hfs, hJ]; exact hFK n s hs z' hz') z hzpos
      have key : |Work.Construction.gRHS α
          (Work.FTS.Galerkin.muDyn α Φ J s) (Work.FTS.Galerkin.lamDyn α Φ J s)
          F Φs' f z θ|
          ≤ (B + 1) * (B + 1) + (4 / α + 6) * (B + 1) ^ 2 + 8 * (B + 1) ^ 2 + 3 * (B + 1) :=
        Work.FTS.StrongEps.EpsWp.gRHS_abs_le_explicit (α := α) (B := B + 1)
          (μ := Work.FTS.Galerkin.muDyn α Φ J s)
          (lam := Work.FTS.Galerkin.lamDyn α Φ J s)
          (F := F) (Φ := Φs') (g := f) hα0 hα1 hB1 hμ hlam
          (by linarith [hb]) (by linarith [hL12F z hzIz]) (by linarith [hL12f n s hs z hzIz])
          (by linarith [hmubar n s hs]) hfk
      convert key using 1
      ring
    -- assemble
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |-(Work.Coercivity.LGammaT α f z θ)| ≤ 28 * B + 32 * B ^ 2 := by
      simpa using hLG
    linarith [h1, hLG, hGR]

theorem epsWP_sup_le_fam {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hT : 0 ≤ T)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p : ℝ × ℝ, p ∈ K →
      |Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ B := by
  obtain ⟨B₀, hB₀nn, hbnd₀⟩ :=
    epsWP_blocks_bnd_fam (α := α) (C₀ := C₀) (Cs := Cs) (Ce := Ce) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) (G := G) (ε := ε) hα hε hT hEll hstar hC hb4 hb6 hK hKQ
  obtain ⟨⟨BL, hBLnn, hL12⟩, ⟨BT, hBTnn, hL12T⟩, ⟨BF, hBFnn, hFK⟩, ⟨Bm, hBmnn, hmubar⟩⟩ :=
    epsWP_hyp_bounds_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T) (ρ := ρ)
      (Φs := Φs) (E := E) (G := G) (ε := ε) hα hEll hstar hC hb4 hb6
  obtain ⟨B₂, hB₂pos, hB₂⟩ := L12_Fstar_abs_le
  set B : ℝ := B₀ + BL + BT + BF + Bm + B₂ + 10 with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  have hB₀le : B₀ ≤ B := by rw [hBdef]; linarith [hBLnn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  have hBLle : BL ≤ B := by rw [hBdef]; linarith [hB₀nn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  have hBTle : BT ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBFnn, hBmnn, hB₂pos.le]
  have hBFle : BF ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBmnn, hB₂pos.le]
  have hBmle : Bm ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hB₂pos.le]
  have hB₂le : B₂ ≤ B := by rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hBmnn]
  have h10le : (10 : ℝ) ≤ B := by
    rw [hBdef]; linarith [hB₀nn, hBLnn, hBTnn, hBFnn, hBmnn, hB₂pos.le]
  obtain ⟨B', hB'pos, hB'bnd⟩ :=
    epsWP_abs_le_on_compact_fam (α := α) (C₀ := C₀) (B := B) (T := T) (ρ := ρ)
    (Φs := Φs) (E := E) (G := G) (ε := ε) hα hε hBnn hml hC hb4 hK hKQ
    (fun n s hs z θ hzθ => le_trans (hbnd₀ n s hs z θ hzθ) hB₀le)
    (fun z θ hzθ => by
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
      exact le_trans (coef_abs_le hα hc1 z θ (le_of_lt hz) ⟨le_of_lt hθ0, le_of_lt hθ1⟩).1 h10le)
    (fun z θ hzθ => by
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hzθ)
      exact le_trans (coef_abs_le hα hc1 z θ (le_of_lt hz) ⟨le_of_lt hθ0, le_of_lt hθ1⟩).2 h10le)
    (fun n s hs z hz => le_trans (hL12 n s hs z hz) hBLle)
    (fun n s hs => le_trans (hL12T n s hs) hBTle)
    (fun z hz => le_trans (hB₂ α hα z hz) hB₂le)
    (fun n s hs z hz => le_trans (hFK n s hs z hz) hBFle)
    (fun n s hs => le_trans (hmubar n s hs) hBmle)
  exact ⟨B', hB'pos, fun n s hs p hp => hB'bnd n s hs p.1 p.2 hp⟩

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP.thLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.thHol_proved` — the NEW clause of the repaired `VelPkg` (open producer)

RESTATED 2026-10-11 (`cbc/fts_thlip_o1_plans.md` ITEM A): `VelPkg.thLip` (θ-Lipschitz) became
`VelPkg.thHol` (θ-Hölder, `ThHol`), and `thLip_proved` became `thHol_proved` (A8). The full
Lipschitz `cs7` half below is NOT needed any more; the Hölder route needs no new analysis
(leaves A1a–A7 in `FTS_RegExport/THL/Leaves.lean`). History of the old clause:

Lead install 2026-10-11 (`cbc/fts_velpkg_fix.md` + `cbc/fts_velpkg_fix_REVIEW.md`). The repaired
`RegExportIface.VelPkg` = the area's `VelPkgOpen` (open-θ `bnd`/`vz0`/`cont`, no axis clause) +
`thLip`. The RX-VP split is `RXVP3.velPkgOpen_proved` + `thLip_proved` (below) → `velPkg`.

Route (REVIEW §3):
* `Vz7` half — from `dbnd`'s `|pth Vz7| ≤ M` + `θ`-differentiability (`c2` on `Q0`) by the mean
  value theorem on the convex `Ioo 0 (π/2)`; no new analysis (even global in `z`).
* `cs7` half — NEW analytic content, research-level, STRONGER than `dbnd`: in
  `Rop Φ̃ = (2 sinθ Φ̃ + αG sinθ z∂_zΦ̃ + cosθ ∂_θΦ̃)/cosθ` the `Φ̃` terms need only `∂²_θΦ̃`
  bounded (with `Φ̃(π/2) = 0`: `B − xB' = O(x²)`), but the term `αG·tanθ·D_zΦ̃` needs `∂²_θ(z∂_zΦ̃)`
  bounded up to both edges — one `z`-derivative beyond `dbnd` (the same missing near-axis sup
  estimates as `dbnd`/`vanish0`). Physically true: `D_z` commutes with `bslOp`, `D_zF ~ Γ ~ x^{2α}`
  gives `D_zΦ̃ = A_z·x + O(x^{2+2α})`, `x = π/2 − θ`; regular near `θ = 0`.
* Optional weaker variant: a Hölder `θ`-modulus `|V θ − V θ'| ≤ K|θ−θ'|^β`, `β ∈ (0,1]`, which needs
  only `C^{1,β}` of `D_zΦ̃` (requires a ~20-line change of `lip_edge_*` to a Cauchy-limit argument).
-/

namespace Work.FTS_RegExport.RXVP

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **A8 = RX-VP / `thHol` (OPEN; RESTATED 2026-10-11 from `thLip_proved`,
`cbc/fts_thlip_o1_plans.md` ITEM A)**: the `VelPkg.thHol` clause at `(gS α (tauExt g), psiR)`, same
hypotheses as `RegExportIface.velPkg`. Route (~30 lines): `β = pExp α / 20`; the `cs7` half is
`THL.cs7_theta_holder` (A6, a global constant, so any `δ` works), the `Vz7` half is
`THL.vz7_thHol` (A7). Leaves: `FTS_RegExport/THL/Leaves.lean`. -/
theorem thHol_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ThHol (Vz7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))) S β ∧
      ThHol (cs7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))) S β := by
  intro S hS
  have hp : 0 < pExp α / 20 := by
    have := Work.FTS.Regularity.pExp_pos hα
    linarith
  have hp1 : pExp α / 20 ≤ 1 := by
    have := Work.FTS.Regularity.pExp_le_one hα13
    linarith
  refine ⟨pExp α / 20, hp, hp1, ?_, ?_⟩
  · exact Work.FTS_RegExport.THL.L.vz7_thHol (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK
      hμ S hS
  · obtain ⟨K, hK, hcs⟩ := Work.FTS_RegExport.THL.cs7_theta_holder (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
    intro z₀ _
    exact ⟨K, hK, 1, one_pos, fun τ hτ z hz _ θ hθ θ' hθ' => hcs τ hτ z hz θ hθ θ' hθ'⟩

end Work.FTS_RegExport.RXVP
end
