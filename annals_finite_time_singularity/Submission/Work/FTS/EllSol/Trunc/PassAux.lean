/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Infrastructure for the truncation passage `flat2DAgmon_of_nice`

This module collects the elementary facts needed to pass from the "nice" (compactly
supported in `t`) case `Work.FTS.EllSol.Trunc.NiceBound` to the general case:
weight endpoint values, a.e. strong measurability of strip-continuous functions,
`NiceFlat` for the cutoff multiples, and the bridge between iterated and product
integrals.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.GalBasis.FamEAux.Basic
import Submission.Work.FTS.EllSol.Trunc.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## The weights at the endpoints of `Iθ` -/

theorem sin_two_zero : Real.sin (2 * (0 : ℝ)) = 0 := by simp

theorem sin_two_pi_div_two : Real.sin (2 * (Real.pi / 2)) = 0 := by
  rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]

theorem neg_eta_ne_zero : -(Work.Spaces.eta) ≠ 0 := by
  rw [Work.Spaces.eta]; norm_num

theorem wE_zero : FlatFT.wE 0 = 0 := by
  rw [FlatFT.wE_def, sin_two_zero]
  exact Real.zero_rpow neg_eta_ne_zero

theorem wE_pi_div_two : FlatFT.wE (Real.pi / 2) = 0 := by
  rw [FlatFT.wE_def, sin_two_pi_div_two]
  exact Real.zero_rpow neg_eta_ne_zero

theorem wA_exp_ne_zero {α : ℝ} (hα : α < 10) : 2 - Work.Spaces.gam α ≠ 0 := by
  intro h
  rw [Work.Spaces.gam] at h
  linarith

theorem wA_zero_of_lt {α : ℝ} (hα : α < 10) : FlatFT.wA α 0 = 0 := by
  rw [FlatFT.wA_def, sin_two_zero]
  exact Real.zero_rpow (wA_exp_ne_zero hα)

theorem wA_pi_div_two_of_lt {α : ℝ} (hα : α < 10) : FlatFT.wA α (Real.pi / 2) = 0 := by
  rw [FlatFT.wA_def, sin_two_pi_div_two]
  exact Real.zero_rpow (wA_exp_ne_zero hα)

/-! ## The strip `univ ×ˢ Ioo 0 (π/2)` -/

theorem isOpen_strip : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  isOpen_univ.prod isOpen_Ioo

theorem mem_strip {t θ : ℝ} (h : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (t, θ) ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := ⟨trivial, h⟩

/-! ## Almost everywhere strong measurability of strip-continuous functions -/

/-- A function continuous on the open strip `ℝ × (0,π/2)` is a.e. strongly measurable for the
restriction of Lebesgue measure to `univ ×ˢ Iθ` (the strip and that set differ by a null set). -/
theorem aesm_strip {h : ℝ × ℝ → ℝ}
    (hh : ContinuousOn h ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable h (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Set.univ ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume] (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq EventuallyEq.rfl hθ
  have hmeas := MeasureTheory.Measure.restrict_congr_set hprod
  exact hmeas ▸ hh.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioo)

/-- The curried partial derivatives of a `C²` function are continuous on the open strip. -/
theorem continuousOn_uncurry_pz_pz {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz g)))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le isOpen_strip 0
    (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le isOpen_strip 1 hg)).continuousOn

theorem continuousOn_uncurry_pth_pth {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth g)))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 0
    (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 1 hg)).continuousOn

theorem continuousOn_uncurry_pz_pth {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth g)))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le isOpen_strip 0
    (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 1 hg)).continuousOn

theorem continuousOn_uncurry_pz {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz g))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le isOpen_strip 1 hg).continuousOn

theorem continuousOn_uncurry_pth {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth g))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le isOpen_strip 1 hg).continuousOn

/-! ## Continuity of the angular weights on the strip -/

theorem continuousOn_sin_two :
    ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn

theorem sin_two_ne_zero_of_mem_strip {p : ℝ × ℝ}
    (hp : p ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    Real.sin (2 * p.2) ≠ 0 := by
  have h2 : 0 < 2 * p.2 := by linarith [hp.2.1]
  have h3 : 2 * p.2 < Real.pi := by linarith [hp.2.2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2 h3)

theorem continuousOn_wE_comp :
    ContinuousOn (fun p : ℝ × ℝ => FlatFT.wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h := continuousOn_sin_two.rpow_const (p := -(Work.Spaces.eta))
    (fun p hp => Or.inl (sin_two_ne_zero_of_mem_strip hp))
  simpa only [FlatFT.wE_def] using h

theorem continuousOn_wA_comp (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => FlatFT.wA α p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h := continuousOn_sin_two.rpow_const (p := 2 - Work.Spaces.gam α)
    (fun p hp => Or.inl (sin_two_ne_zero_of_mem_strip hp))
  simpa only [FlatFT.wA_def] using h

/-! ## The bridge between iterated and product integrals -/

theorem setIntegral_univ_prod_Iθ_eq_iterated {f : ℝ → ℝ → ℝ}
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, f p.1 p.2)
      = ∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, f t θ := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.setIntegral_prod _ hf

/-! ## `NiceFlat` for the cutoff multiples -/

theorem niceFlat_chi_mul {g : ℝ → ℝ → ℝ} {N : ℝ} (hN : 0 < N)
    (hg : ContDiffOn ℝ 2 (Function.uncurry g)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hg0 : ∀ t : ℝ, g t 0 = 0) (hgpi : ∀ t : ℝ, g t (Real.pi / 2) = 0) :
    FlatFT.NiceFlat (fun t θ => chi N t * g t θ) := by
  have huncurry : Function.uncurry (fun t θ => chi N t * g t θ)
      = fun p : ℝ × ℝ => chi N p.1 * g p.1 p.2 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [huncurry]
    have h1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => chi N p.1) :=
      (chi_contDiff 2 N).comp contDiff_fst
    exact h1.contDiffOn.mul hg
  · intro t; show chi N t * g t 0 = 0; rw [hg0 t, mul_zero]
  · intro t; show chi N t * g t (Real.pi / 2) = 0; rw [hgpi t, mul_zero]
  · refine ⟨2 * N, ?_⟩
    intro t θ ht
    have h2 : 2 * N ≤ |t| := le_of_lt ht
    show chi N t * g t θ = 0
    rw [chi_eq_zero hN h2, zero_mul]

end

end Work.FTS.EllSol.Trunc
