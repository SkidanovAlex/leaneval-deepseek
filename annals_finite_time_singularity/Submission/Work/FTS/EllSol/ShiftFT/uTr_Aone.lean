import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.Trunc.PassAux2
import Submission.Work.FTS.EllSol.Trunc.WindowBase
import Submission.Work.FTS.EllSol.ShiftFT.uTrAone.GcAbsLe
import Submission.Work.FTS.EllSol.ShiftFT.uTrAone.GcAesm
import Submission.Work.FTS.EllSol.ShiftFT.uTrAone.derivPhiTrGcLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The shifted `A₁` slot of the truncation `uTr`

`Work.FTS.EllSol.ShiftFT.uTr N b u = phiTr N · Gc N b u` is the truncated data used in
`Work.FTS.EllSol.ShiftFT.shiftedFlat_of_nice`: `Gc N b u` is the (backward) primitive of
`chi N · L_b u` (`L_b = ∂_t - b`) and `phiTr N = chi (4096·N)` cuts off the exponentially
decaying tail `e^{bt}·A(θ)` of `Gc`, which is a `b`-harmonic mode and hence invisible to `L_b`.

This file proves the `A₁`-slot bound: the `L_b`-energy of `uTr N b u` is controlled by the
`L_b`-energy of `u` itself, uniformly in `N ≥ 2`,

`∫∫ (L_b (uTr N b u))² σ_η ≤ K · ∫∫ (L_b u)² σ_η`.

The proof is `(a+b)² ≤ 2a² + 2b²` applied to the product rule
`L_b (phiTr N · Gc) = (phiTr N)' · Gc + phiTr N · L_b (Gc)` together with
`L_b (Gc) = chi N · L_b u` (`Work.FTS.EllSol.ShiftFT.Gc_sh`).  The first slot is bounded by
`∫∫(L_b u)²σ_η` (`phiTr`, `chi ∈ [0,1]`), the second – the truncation error – is the content of
`derivPhiTrGcLe`, which uses the support of `(phiTr N)'` and the fact that off the truncation
window `Gc` is controlled by `L_b u` (`GcAbsLe`).
-/

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-! ## §1  Elementary facts about the cutoffs -/

/-- `chi N` is locally constant `1` on `(-N,N)` (for `N > 0`). -/
theorem uTrAone_deriv_chi_eq_zero_of_lt {N t : ℝ} (hN : 0 < N) (ht : |t| < N) :
    deriv (Trunc.chi N) t = 0 := by
  have hopen : IsOpen {s : ℝ | |s| < N} := isOpen_lt continuous_abs continuous_const
  have hev : (Trunc.chi N) =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact Trunc.chi_eq_one hN (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-- `deriv (phiTr N)` vanishes on `(-4096N, 4096N)`. -/
theorem uTrAone_deriv_phiTr_eq_zero_of_lt {N t : ℝ} (hN : 0 < N) (ht : |t| < 4096 * N) :
    deriv (phiTr N) t = 0 :=
  uTrAone_deriv_chi_eq_zero_of_lt (N := 4096 * N) (by linarith) ht

/-- `deriv (phiTr N)` vanishes off `(-8192N, 8192N)`. -/
theorem uTrAone_deriv_phiTr_eq_zero_of_gt {N t : ℝ} (hN : 0 < N) (ht : 8192 * N < |t|) :
    deriv (phiTr N) t = 0 :=
  Trunc.deriv_chi_eq_zero_of_gt (N := 4096 * N) (by linarith) (by linarith)

/-- `|deriv (phiTr N) t| ≤ K/(4096N)` whenever `|deriv tk| ≤ K`. -/
theorem uTrAone_abs_deriv_phiTr_le {N K : ℝ}
    (hK : ∀ t : ℝ, |deriv Trunc.tk t| ≤ K) (hN : 0 < N) (t : ℝ) :
    |deriv (phiTr N) t| ≤ K / (4096 * N) :=
  Trunc.abs_deriv_chi_le hK (by linarith) t

/-- The integration domain `ℝ × Iθ` differs from the open strip by a null set. -/
theorem uTrAone_SI_ae_eq_strip :
    (Set.univ ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume] ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm

/-! ## §2  The `t`-derivative of the primitive `Gc` -/

/-- `t ↦ Gc N b u t θ` has `t`-derivative `b·Gc + chi N t·(L_b u)` on the open strip.

This is the `HasDerivAt` form of `Work.FTS.EllSol.ShiftFT.Gc_sh`
(`L_b (Gc N b u) = chi N · L_b u`), obtained by the product rule applied to
`Gc = chi N · u + e^{bt}·∫_t^{2N} e^{-bs}(chi N)' u` together with the fundamental theorem of
calculus for the variable lower limit. -/
theorem uTrAone_Gc_hasDerivAt (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun t' => Gc N b u t' θ)
        (b * Gc N b u t θ
          + Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ)) t := by
  intro t θ hθ
  have hchi2 : ContDiff ℝ 2 (Trunc.chi N) := Trunc.chi_contDiff 2 N
  have hchiD : DifferentiableAt ℝ (Trunc.chi N) t := hchi2.differentiable (by norm_num) t
  have hchic : Continuous (deriv (Trunc.chi N)) := hchi2.continuous_deriv (by norm_num)
  have hmap : Set.MapsTo (fun s : ℝ => (s, θ)) Set.univ
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
  have hpair : ContDiffOn ℝ 2 (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hslice : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) Set.univ := by
    have h := hu.comp hpair hmap
    simpa [Function.comp_def, Function.uncurry] using h
  have hsliceDiff : DifferentiableAt ℝ (fun s : ℝ => u s θ) t :=
    (hslice.differentiableOn (by norm_num)).differentiableAt (by simp)
  have hsliceC : Continuous (fun s : ℝ => u s θ) := continuousOn_univ.mp hslice.continuousOn
  have hslice_deriv : HasDerivAt (fun s : ℝ => u s θ) (deriv (fun s : ℝ => u s θ) t) t :=
    hsliceDiff.hasDerivAt
  have hFd : HasDerivAt (fun s : ℝ => Trunc.chi N s * u s θ)
      (deriv (Trunc.chi N) t * u t θ
        + Trunc.chi N t * deriv (fun s : ℝ => u s θ) t) t :=
    hchiD.hasDerivAt.mul hslice_deriv
  have hexpD : HasDerivAt (fun s : ℝ => Real.exp (b * s)) (b * Real.exp (b * t)) t := by
    have h : HasDerivAt (fun s : ℝ => b * s) b t := by
      have h' := (hasDerivAt_id t).const_mul b
      simpa using h'
    simpa [mul_comm] using h.exp
  have hint_cont : Continuous (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ) := by
    have h1 : Continuous (fun s : ℝ => Real.exp (-(b * s))) := by fun_prop
    exact (h1.mul hchic).mul hsliceC
  have hH : HasDerivAt (fun v : ℝ => ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
      (-(Real.exp (-(b * t)) * deriv (Trunc.chi N) t * u t θ)) t :=
    intervalIntegral.integral_hasDerivAt_left (hint_cont.intervalIntegrable t (2 * N))
      (hint_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hint_cont.continuousAt
  have hEHd : HasDerivAt (fun v : ℝ => Real.exp (b * v) * ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
      (b * Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
        + Real.exp (b * t) * (-(Real.exp (-(b * t))
            * deriv (Trunc.chi N) t * u t θ))) t :=
    hexpD.mul hH
  have hsumd : HasDerivAt (fun v : ℝ => Trunc.chi N v * u v θ
        + Real.exp (b * v) * ∫ s in v..(2 * N),
          Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
      ((deriv (Trunc.chi N) t * u t θ
          + Trunc.chi N t * deriv (fun s : ℝ => u s θ) t)
        + (b * Real.exp (b * t) * (∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ)
          + Real.exp (b * t) * (-(Real.exp (-(b * t))
              * deriv (Trunc.chi N) t * u t θ)))) t :=
    hFd.add hEHd
  have hexpneg : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  refine hsumd.congr_deriv ?_
  have hGct : Gc N b u t θ = Trunc.chi N t * u t θ
      + Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ := rfl
  have hpzt : Work.Spaces.pz u t θ = deriv (fun s : ℝ => u s θ) t := rfl
  rw [hGct, hpzt]
  linear_combination (-(deriv (Trunc.chi N) t * u t θ)) * hexpneg

/-! ## §3  The product rule for `uTr` -/

/-- The shifted operator applied to the truncation: for `θ ∈ (0,π/2)`,
`L_b (uTr N b u) = (phiTr N)' · Gc + phiTr N · chi N · L_b u`. -/
theorem uTrAone_uTr_sh (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (uTr N b u) t θ - b * uTr N b u t θ
        = deriv (phiTr N) t * Gc N b u t θ
          + phiTr N t * (Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ)) := by
  intro t θ hθ
  have hphi : HasDerivAt (fun v : ℝ => phiTr N v) (deriv (phiTr N) t) t :=
    ((phiTr_contDiff 1 N).differentiable (by norm_num) t).hasDerivAt
  have hGc := uTrAone_Gc_hasDerivAt N b u hu t θ hθ
  have hmul := hphi.mul hGc
  have hmain : deriv (fun v : ℝ => phiTr N v * Gc N b u v θ) t
      = deriv (phiTr N) t * Gc N b u t θ
        + phiTr N t * (b * Gc N b u t θ
            + Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ)) := hmul.deriv
  have hkey : Work.Spaces.pz (uTr N b u) t θ - b * uTr N b u t θ
      = deriv (fun v : ℝ => phiTr N v * Gc N b u v θ) t
        - b * (phiTr N t * Gc N b u t θ) := by
    show deriv (fun v : ℝ => uTr N b u v θ) t - b * uTr N b u t θ = _
    rfl
  rw [hkey, hmain]
  ring

/-! ## §4  The `phiTr · chi N · L_b u` slot -/

/-- The `chi N · L_b u` slot of `L_b (uTr N b u)`: its weighted energy is at most that of
`L_b u` itself, because `0 ≤ phiTr N ≤ 1` and `0 ≤ chi N ≤ 1`. -/
theorem uTrAone_B_slot (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ =>
        (phiTr N p.1 * (Trunc.chi N p.1
          * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (phiTr N p.1 * (Trunc.chi N p.1
          * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      ≤ (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2) := by
  have hSI : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hwEnn : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      0 ≤ FlatFT.wE p.2 := by
    filter_upwards [ae_restrict_mem (μ := volume) hSI] with p hp
    exact FlatFT.wE_nonneg hp.2
  have hv_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (Trunc.aesm_strip (Trunc.continuousOn_uncurry_pz hu)).sub
      ((Trunc.aesm_strip hu.continuousOn).const_mul b)
  have hB_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have hphi : AEStronglyMeasurable (fun p : ℝ × ℝ => phiTr N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((phiTr_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hchi : AEStronglyMeasurable (fun p : ℝ × ℝ => Trunc.chi N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((Trunc.chi_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hwE : AEStronglyMeasurable (fun p : ℝ × ℝ => FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip Trunc.continuousOn_wE_comp
    exact ((hphi.mul (hchi.mul hv_aesm)).pow 2).mul hwE
  have hBnn : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      0 ≤ (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2 := by
    filter_upwards [hwEnn] with p hp
    exact mul_nonneg (sq_nonneg _) hp
  have hle : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2
      ≤ (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2 := by
    filter_upwards [hwEnn] with p hp
    set w : ℝ := Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2 with hw
    have h1 : (0 : ℝ) ≤ phiTr N p.1 := phiTr_nonneg N p.1
    have h2 : phiTr N p.1 ≤ 1 := phiTr_le_one N p.1
    have h3 : (0 : ℝ) ≤ Trunc.chi N p.1 := Trunc.chi_nonneg N p.1
    have h4 : Trunc.chi N p.1 ≤ 1 := Trunc.chi_le_one N p.1
    have h5 : (0 : ℝ) ≤ phiTr N p.1 * Trunc.chi N p.1 := mul_nonneg h1 h3
    have h6 : phiTr N p.1 * Trunc.chi N p.1 ≤ 1 := by nlinarith
    have h7 : (phiTr N p.1 * Trunc.chi N p.1) ^ 2 ≤ 1 := by nlinarith
    calc (phiTr N p.1 * (Trunc.chi N p.1 * w)) ^ 2 * FlatFT.wE p.2
        = (phiTr N p.1 * Trunc.chi N p.1) ^ 2 * (w ^ 2 * FlatFT.wE p.2) := by ring
      _ ≤ 1 * (w ^ 2 * FlatFT.wE p.2) :=
          mul_le_mul_of_nonneg_right h7 (mul_nonneg (sq_nonneg _) hp)
      _ = w ^ 2 * FlatFT.wE p.2 := by ring
  have hBint : IntegrableOn (fun p : ℝ × ℝ =>
      (phiTr N p.1 * (Trunc.chi N p.1
        * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    refine Integrable.mono' hI hB_aesm ?_
    filter_upwards [hBnn, hle] with p hnn hleq
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hleq
  refine ⟨hBint, ?_⟩
  refine integral_mono_ae hBint hI ?_
  filter_upwards [hle] with p hple
  exact hple

/-! ## §5  The `A₁` slot: assembly -/

theorem uTr_Aone (b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N ≥ (2 : ℝ),
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
          - b * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
            - b * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ K * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) := by
  obtain ⟨Ktk, hKtk0, hKtkbd⟩ := Trunc.exists_bound_deriv_tk
  refine ⟨2 + 2 * Ktk ^ 2, by nlinarith [sq_nonneg Ktk], fun N hN => ?_⟩
  have hNpos : 0 < N := by linarith
  have hSI : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hwEnn : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      0 ≤ FlatFT.wE p.2 := by
    filter_upwards [ae_restrict_mem (μ := volume) hSI] with p hp
    exact FlatFT.wE_nonneg hp.2
  -- ### the a.e. product rule on the integration domain
  have hrule : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2
        = deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2)) := by
    rw [Measure.restrict_congr_set uTrAone_SI_ae_eq_strip]
    filter_upwards [ae_restrict_mem Trunc.isOpen_strip.measurableSet] with p hp
    exact uTrAone_uTr_sh N b u hu p.1 p.2 hp.2
  -- ### the two slots
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Gc N b u p.1 p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.ShiftFT.uTrAone.GcAesm N b u hu
  obtain ⟨hAint, hAle⟩ :=
    Work.FTS.EllSol.ShiftFT.uTrAone.derivPhiTrGcLe N b Ktk u hN hKtkbd hu hI hmeas
      (Work.FTS.EllSol.ShiftFT.uTrAone.GcAbsLe N b u hNpos hb hu)
  obtain ⟨hBint, hBle⟩ := uTrAone_B_slot N b u hu hI
  have hF0eq : (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2) ^ 2
          * FlatFT.wE p.2)
      =ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ =>
        (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    filter_upwards [hrule] with p hp
    rw [hp]
  -- ### pointwise `(a+b)² ≤ 2a² + 2b²`
  have hF1le : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2
      ≤ 2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    filter_upwards [hwEnn] with p hp
    set X : ℝ := deriv (phiTr N) p.1 * Gc N b u p.1 p.2 with hX
    set Y : ℝ := phiTr N p.1 * (Trunc.chi N p.1
      * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2)) with hY
    have hsq : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
    calc (X + Y) ^ 2 * FlatFT.wE p.2
        ≤ (2 * X ^ 2 + 2 * Y ^ 2) * FlatFT.wE p.2 :=
          mul_le_mul_of_nonneg_right hsq hp
      _ = 2 * (X ^ 2 * FlatFT.wE p.2) + 2 * (Y ^ 2 * FlatFT.wE p.2) := by ring
  have h2A2Bint : IntegrableOn (fun p : ℝ × ℝ =>
      2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2))
      (Set.univ ×ˢ Work.Spaces.Iθ) :=
    (hAint.const_mul 2).add (hBint.const_mul 2)
  have hF1_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have hdphi : AEStronglyMeasurable (fun p : ℝ × ℝ => deriv (phiTr N) p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      (((phiTr_contDiff 1 N).continuous_deriv le_rfl).comp continuous_fst).aestronglyMeasurable
    have hphi : AEStronglyMeasurable (fun p : ℝ × ℝ => phiTr N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((phiTr_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hchi : AEStronglyMeasurable (fun p : ℝ × ℝ => Trunc.chi N p.1)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      ((Trunc.chi_contDiff 0 N).continuous.comp continuous_fst).aestronglyMeasurable
    have hpz : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip (Trunc.continuousOn_uncurry_pz hu)
    have hu' : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip hu.continuousOn
    have hwE : AEStronglyMeasurable (fun p : ℝ × ℝ => FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Trunc.aesm_strip Trunc.continuousOn_wE_comp
    exact (((hdphi.mul hmeas).add
      (hphi.mul (hchi.mul (hpz.sub (hu'.const_mul b))))).pow 2).mul hwE
  have hF1norm : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      ‖(deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2‖
      ≤ 2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    filter_upwards [hF1le, hwEnn] with p hpl hpm
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpm)]
    exact hpl
  have hF1int : IntegrableOn (fun p : ℝ × ℝ =>
      (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) :=
    Integrable.mono' h2A2Bint hF1_aesm hF1norm
  have hF0int : IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2) ^ 2
        * FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
    Integrable.congr hF1int hF0eq.symm
  refine ⟨hF0int, ?_⟩
  have hmain : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pz (uTr N b u) p.1 p.2 - b * uTr N b u p.1 p.2) ^ 2
          * FlatFT.wE p.2)
      = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2 :=
    integral_congr_ae hF0eq
  have hmono : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (deriv (phiTr N) p.1 * Gc N b u p.1 p.2
          + phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)
      ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
          + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)) :=
    integral_mono_ae hF1int h2A2Bint hF1le
  have hsplit : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (2 * ((deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
          + 2 * ((phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2)))
      = 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (deriv (phiTr N) p.1 * Gc N b u p.1 p.2) ^ 2 * FlatFT.wE p.2)
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (phiTr N p.1 * (Trunc.chi N p.1
              * (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2))) ^ 2 * FlatFT.wE p.2) := by
    rw [MeasureTheory.integral_add (hAint.const_mul 2) (hBint.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have harith : 2 * (Ktk ^ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2))
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2)
      = (2 + 2 * Ktk ^ 2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * FlatFT.wE p.2) := by ring
  linarith [hmain.le, hmono, hsplit.le, hAle, hBle, harith]

end

end Work.FTS.EllSol.ShiftFT
