import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS.FinalV2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.l12_zero_plainE`

The zero mode of `L₁₂` passes to the limit along the class-C approximants of
`Work.FTS.FinalV2.LimApprox` — the **plain-`E`** form of
`Work.FTS_RegExport.RXB.l12_zero_lim_proved`, whose assembly
`Work.FTS_RegExport.RXB.l12_zero_lim_of_bounds` is stated for a *linear* `E : Fn →ₗ[ℝ] Fn`.

Nothing in the assembly uses the linearity of `E`: `E` occurs in `LimApprox` only as a plain
function (in the `muDyn`-convergence clause, which the argument never reads) and the proof only
consumes the class-C approximants `gn`, their uniform `ℋ⁴`-bound and their jet convergence.
We therefore repeat the assembly verbatim for `E : Fn → Fn`, fed with the two analytic inputs of
the directory:

* `sup_bound_all_alpha` — the interior `L^∞`–`ℋ⁴` trade-off `f² ≤ C|f|²_{ℋ⁴}` (`SupBnd`);
* `l12dens_weighted_bound` — the weighted density bound `|L₁₂dens f s| ≤ C(√s/(1+s)²)|f|_{ℋ⁴}`
  (`DensBnd`), which turns the uniform `ℋ⁴`-bound of the approximants into an `L¹(ds)` majorant.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_StreamBdry.SB4

set_option autoImplicit false

/-- **`RX-B`, plain-`E` form**: the assembly of
`Work.FTS_RegExport.RXB.l12_zero_lim_of_bounds` with an arbitrary (not necessarily linear) `E`.

Given the two analytic inputs `SupBnd` (interior `L^∞`–`ℋ⁴` bound) and `DensBnd` (weighted bound
on the zero mode) at every `α > 0`, every `τ ≥ 0` has `L₁₂(slice g τ)(0) = 0` for a family `g`
which is the pointwise limit of class-C approximants with a uniform `ℋ⁴`-bound (`LimApprox`). -/
theorem l12_zero_lim_of_bounds_plainE {αG C₀ : ℝ} (hα : 0 < αG)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsupAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ Work.FTS_RegExport.RXB.SupBnd α C)
    (hdenAll : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ Work.FTS_RegExport.RXB.DensBnd α C)
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by
  intro τ hτ
  obtain ⟨Csup, hCsup, hsup⟩ := hsupAll αG hα
  obtain ⟨Cden, hCden, hden⟩ := hdenAll αG hα
  obtain ⟨gn, B, L, hcls, hlip, hjet, hmu⟩ := hA (max τ 1 + 1) (by
    have := le_max_right τ 1
    linarith)
  have hτT : τ ∈ Set.Icc (0:ℝ) (max τ 1 + 1) := by
    refine ⟨hτ, ?_⟩
    have := le_max_left τ 1
    linarith
  -- the class data of the approximants
  have hclass : ∀ n, Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) :=
    fun n => (hcls n τ hτT).1
  have hN : ∀ n, Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
    fun n => (hcls n τ hτT).2.1
  have hΛ : 0 ≤ C₀ * αG ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg αG 4 _) (hN 0)
  have hcls' : ∀ n, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := fun n =>
    ⟨(hclass n).reg,
     Work.FTS.OpenPkg.HkMem_mono_open (hclass n).reg 4 (by norm_num) (hclass n).mem,
     Work.FTS.ClassC.bdryTraces_mono (by norm_num) (hclass n).tr⟩
  have hjet' : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < Real.pi / 2 →
      Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ s θ) atTop
        (𝓝 (Work.FTS.Galerkin.slice g τ s θ)) := by
    intro s θ hs hθ hθ'
    have h := hjet τ hτT 0 0 (by norm_num) s θ ⟨hs, hθ, hθ'⟩
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
      Work.Spaces.DzIter_zero] using h
  have hzero : ∀ n, Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0 = 0 :=
    fun n => (hclass n).l12_zero
  -- the `L¹(ds)` majorant
  set M : ℝ → ℝ := fun s => Cden * (Real.sqrt s / (1 + s) ^ 2) * (C₀ * αG ^ 2) with hMdef
  have hMint : MeasureTheory.IntegrableOn M (Set.Ioi 0) := by
    have h : MeasureTheory.IntegrableOn
        (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) (Set.Ioi 0) :=
      Work.FTS_RegExport.RXB.integrableOn_sqrt_div_sq.const_mul (Cden * (C₀ * αG ^ 2))
    have hfun : (fun s : ℝ => (Cden * (C₀ * αG ^ 2)) * (Real.sqrt s / (1 + s) ^ 2)) = M := by
      funext s
      simp only [hMdef]
      ring
    rwa [hfun] at h
  -- the dominated convergence theorem in the radial variable
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable (fun z hz => ?_) measurableSet_Ioi
    exact (Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk
      (hcls' n).1 (hcls' n).2.1 hz).continuousWithinAt
  have hconv : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s)
        atTop (𝓝 (Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) s)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs =>
      Work.FTS_RegExport.RXB.tendsto_L12dens_of_sup_bound hΛ hCsup hsup hcls' hN hjet' hs)
  have hbdd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), ∀ n,
      ‖Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s‖ ≤ M s := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs n => ?_)
    have h1 : |Work.Construction.L12dens (Work.FTS.Galerkin.slice (gn n) τ) s|
        ≤ Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      hden _ (hcls' n).1 (hcls' n).2.1 (hcls' n).2.2 s hs
    have h2 : Cden * (Real.sqrt s / (1 + s) ^ 2)
          * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ M s := by
      rw [hMdef]
      exact mul_le_mul_of_nonneg_left (hN n)
        (by positivity)
    rw [Real.norm_eq_abs]
    exact le_trans h1 h2
  have hlim := Work.FTS.StrongEps.L12_tendsto_of_dominated
    (f := fun n => Work.FTS.Galerkin.slice (gn n) τ) (g := Work.FTS.Galerkin.slice g τ)
    (M := M) (ρ := 0) hmeas hconv hbdd hMint
  have h0 : Tendsto (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
      atTop (𝓝 (0:ℝ)) := by
    have hfun : (fun n => Work.Construction.L12 (Work.FTS.Galerkin.slice (gn n) τ) 0)
        = fun _ => (0:ℝ) := funext hzero
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

theorem l12_zero_plainE {αG C₀ : ℝ} (hα : 0 < αG)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 :=
  l12_zero_lim_of_bounds_plainE hα
    (fun α hα => Work.FTS_RegExport.RXB.sup_bound_all_alpha hα)
    (fun α hα => Work.FTS_RegExport.RXB.l12dens_weighted_bound hα)
    hA

end Work.FTS_StreamBdry.SB4
