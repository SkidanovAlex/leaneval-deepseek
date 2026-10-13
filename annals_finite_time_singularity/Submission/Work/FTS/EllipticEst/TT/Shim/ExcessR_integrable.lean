/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability in `z` of the excess radial term of `D_z Ψ`

`DzAux.EXR Ψ k z θ = (D_z^{k+1}Ψ(z,θ)·w(z)/sin(2θ)^{η/2})²` is the one summand of
`HkIntegrand α k (D_z Ψ)` that is neither a summand of `HkIntegrand α k Ψ` nor of
`HkIntegrand α k (D_θΨ)`; here we prove that its `z`-slice integrals are `z`-integrable.

Route: for every angle `θ`, apply the (unconditional, `ℝ≥0∞`-valued) weighted Agmon inequality
`Work.FTS.EllipticEst.TT.rDz_agmon_lintegral_tt` to the *scaled slice*
`h_θ(z) = sin(2θ)^{-η/2}·D_z^kΨ(z,θ)`.  Its three Agmon terms are, by elementary algebra,

* `rDz h_θ = sin(2θ)^{-η/2}·D_z^{k+1}Ψ(·,θ)`,
* `h_θ = sin(2θ)^{-η/2}·D_z^kΨ(·,θ)`,
* `z²h_θ'' = sin(2θ)^{-η/2}·D_z^k(z²∂_z²Ψ)(·,θ)` — here one uses
  `D_z^k(z²∂_z²Ψ) = D_z^{k+2}Ψ - D_z^{k+1}Ψ` (`DzAux.DzIter_zsq_eqOn`) and
  `rDzIter 2 h - rDzIter 1 h = z²h''`,

so that, with the *same* angular factor `sin(2θ)^{-η}`, the Agmon inequality reads

  `α² ∫⁻_z EXR(·,θ) ≤ C (∫⁻_z PR(·,θ) + α⁴ ∫⁻_z ZR(·,θ))`   uniformly in `θ ∈ Iθ`.

No square roots are needed: everything is already in `ℝ≥0∞`.  Tonelli's theorem identifies
`∫⁻_z ofReal(∫_θ EXR)` with `∫⁻_θ ∫⁻_z ofReal(EXR)`, and the two `θ`-integrals on the right are
finite by `hPRlin`/`hZRlin` (the a.e. identification of `∫⁻_z ofReal(PR(·,θ))` with
`ofReal(∫_z PR(·,θ))` being supplied by `hPRae`).  Finally
`MeasureTheory.lintegral_ofReal_ne_top_iff_integrable` turns the finiteness into `IntegrableOn`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.Shim.DzPsiAux
import Submission.Work.FTS.EllipticEst.TT.AgmonTT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.Cert.DzAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
-- `hPRz`, `hZRz` are part of the requested statement but are only used by its consumers.
set_option linter.unusedVariables false

/-! ## The one-dimensional identity `z²h'' = rDzIter 2 h - rDzIter 1 h` -/

/-- `rDzIter 2 h z = z h'(z) + z² h''(z)` for `z > 0`. -/
private lemma rDzIter_two_eq {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) {z : ℝ}
    (hz : 0 < z) :
    Work.FTS.EllipticEst.rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z := by
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) :=
    hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff : DifferentiableAt ℝ (deriv h) z :=
    (hd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hprod : HasDerivAt (fun y : ℝ => y * deriv h y)
      (deriv h z + z * deriv (deriv h) z) z := by
    have h := (hasDerivAt_id z).mul hdiff.hasDerivAt
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  change z * deriv (fun y : ℝ => y * deriv h y) z = _
  rw [hprod.deriv]
  ring

/-! ## The per-angle Agmon bound for the excess term -/

/-- **The excess radial term is controlled by the two input terms, at each fixed angle.**

For `0 < α ≤ 1` and `θ ∈ Iθ`, the weighted Agmon inequality for the scaled slice
`h_θ(z) = sin(2θ)^{-η/2}·D_z^kΨ(z,θ)` gives

  `α² ∫⁻_z EXR Ψ k z θ ≤ C ( ∫⁻_z PR Ψ k z θ + α⁴ ∫⁻_z ZR Ψ k z θ )`,

where `C` is the universal constant of `rDz_agmon_lintegral_tt` and all three integrals are
`∫⁻_z`-integrals over `Iz`. -/
private theorem excess_slice_bound (C : ℝ) (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (k : ℕ)
    (hAg : ∀ (h : ℝ → ℝ), ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.rDz h z ^ 2))
        ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))
            + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))))
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ))
      ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
          + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ))) := by
  set c : ℝ := (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹ with hc
  set h : ℝ → ℝ := fun z => c * Work.Spaces.DzIter k Ψ z θ with hh
  have hhcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) := by
    have h1a : ContDiffOn ℝ ⊤ (fun z => Work.Spaces.DzIter k Ψ z θ) (Set.Ioi (-1)) :=
      Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.DzIter k Ψ)
        (Work.Spaces.SmoothNbhd.DzIter hsm k) hθ
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => Work.Spaces.DzIter k Ψ z θ)
        (Set.Ioi 0) :=
      (h1a.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).of_le le_top
    rw [hh]
    exact contDiffOn_const.mul h1
  have h2 := hAg h hhcd
  have e1 : Work.FTS.EllipticEst.rDzIter 1 h
      = fun z => c * Work.FTS.EllipticEst.rDzIter 1 (fun z => Work.Spaces.DzIter k Ψ z θ) z := by
    rw [hh]
    exact Work.FTS.EllipticEst.rDz_const_mul c _
  have e2 : Work.FTS.EllipticEst.rDzIter 2 h
      = fun z => c * Work.FTS.EllipticEst.rDzIter 2 (fun z => Work.Spaces.DzIter k Ψ z θ) z := by
    rw [hh]
    exact rDzIter_two_const_mul c _
  have e3 : Work.FTS.EllipticEst.rDzIter 1 (fun z => Work.Spaces.DzIter k Ψ z θ)
      = fun z => Work.Spaces.DzIter (k + 1) Ψ z θ := rDzIter_one_slice Ψ k θ
  have e4 : Work.FTS.EllipticEst.rDzIter 2 (fun z => Work.Spaces.DzIter k Ψ z θ)
      = fun z => Work.Spaces.DzIter (k + 2) Ψ z θ := rDzIter_two_slice Ψ k θ
  have iEXRpt : ∀ z, (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h z) ^ 2
      = EXR Ψ k z θ := by
    intro z
    have h1 : Work.FTS.EllipticEst.rDz h z = c * Work.Spaces.DzIter (k + 1) Ψ z θ := by
      simp only [show Work.FTS.EllipticEst.rDz h = Work.FTS.EllipticEst.rDzIter 1 h from rfl,
        e1, e3]
    simp only [h1, EXR, hc]
    rw [div_eq_mul_inv]
    ring
  have iPRpt : ∀ z, (Work.Spaces.w z) ^ 2 * (h z) ^ 2 = PR Ψ k z θ := by
    intro z
    simp only [hh, PR, hc]
    rw [div_eq_mul_inv]
    ring
  have iZRpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 = ZR Ψ k z θ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz : (0 : ℝ) ≤ z) with h0 | hpos
    · subst h0
      simp only [ZR, Work.Spaces.w]
      norm_num
    · have hd2 : ContDiffOn ℝ 2 h (Set.Ioi 0) :=
        hhcd.of_le (by simp [Work.Stability.smoothOrder])
      have hd1 : Work.FTS.EllipticEst.rDzIter 1 h z = z * deriv h z := rfl
      have hr2 := rDzIter_two_eq hd2 hpos
      have hdiff : z ^ 2 * deriv (deriv h) z
          = Work.FTS.EllipticEst.rDzIter 2 h z - Work.FTS.EllipticEst.rDzIter 1 h z := by
        rw [hd1, hr2]
        ring
      have hcz : Work.FTS.EllipticEst.rDzIter 2 h z - Work.FTS.EllipticEst.rDzIter 1 h z
          = c * (Work.Spaces.DzIter (k + 2) Ψ z θ - Work.Spaces.DzIter (k + 1) Ψ z θ) := by
        simp only [e1, e2, e3, e4, hc]
        ring
      have hzsq : Work.Spaces.DzIter (k + 2) Ψ z θ - Work.Spaces.DzIter (k + 1) Ψ z θ
          = Work.Spaces.DzIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
        have h5 := DzIter_zsq_eqOn Ψ hsm k (Work.Spaces.mem_nbhU (Set.mem_Ici.mpr hpos.le) hθ)
        simpa only [Function.uncurry] using h5.symm
      rw [hdiff, hcz, hzsq]
      simp only [ZR, hc]
      rw [div_eq_mul_inv]
      ring
  have hEXReq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDz h z) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ) :=
    MeasureTheory.lintegral_congr (fun z => by rw [iEXRpt z])
  have hPReq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ) :=
    MeasureTheory.lintegral_congr (fun z => by rw [iPRpt z])
  have hZReq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [iZRpt z hz]
  rwa [hEXReq, hPReq, hZReq] at h2

/-! ## The excess radial term of `D_z Ψ` -/

theorem ExcessR_integrable (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hPRz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ) Work.Spaces.Iz)
    (hPRae : Filter.Eventually (fun θ => MeasureTheory.IntegrableOn (fun z =>
      Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ) Work.Spaces.Iz)
      (MeasureTheory.ae (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hPRlin : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Cert.DzAux.PR Ψ k z θ)) < ⊤)
    (hZRz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ) Work.Spaces.Iz)
    (hZRae : Filter.Eventually (fun θ => MeasureTheory.IntegrableOn (fun z =>
      Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ) Work.Spaces.Iz)
      (MeasureTheory.ae (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hZRlin : MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Cert.DzAux.ZR Ψ k z θ)) < ⊤)
    (hEXRsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ k z θ) Work.Spaces.Iθ)
    (hEXRaesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ k p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Cert.DzAux.EXR Ψ k z θ) Work.Spaces.Iz := by
  obtain ⟨C, hCpos, hAgAll⟩ := rDz_agmon_lintegral_tt
  -- the per-angle Agmon bound
  have key : ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ))
        ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
          + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ))) :=
    fun θ hθ => excess_slice_bound C α Ψ hsm k (hAgAll α hα hα1) hθ
  -- a.e. identification of the `z`-`lintegral`s of `PR`, `ZR` with the honest slice integrals
  have hPeq : (fun θ : ℝ => ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ENNReal.ofReal (∫ z in Work.Spaces.Iz, PR Ψ k z θ)) := by
    filter_upwards [hPRae] with θ hθ
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ
      (Filter.Eventually.of_forall (fun z => by simp only [PR]; positivity))).symm
  have hZeq : (fun θ : ℝ => ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ENNReal.ofReal (∫ z in Work.Spaces.Iz, ZR Ψ k z θ)) := by
    filter_upwards [hZRae] with θ hθ
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ
      (Filter.Eventually.of_forall (fun z => by simp only [ZR]; positivity))).symm
  -- measurability of the two `z`-slices of the input terms
  have hPlin : AEMeasurable (fun θ : ℝ =>
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := aesm_zSummand_sq_prod' (0 : ℝ) hsm k
    have h' : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (PR Ψ k p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      simpa only [PR] using h
    exact h'.lintegral_prod_left'
  have hZlin : AEMeasurable (fun θ : ℝ =>
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := aesm_zSummand_sq_prod' (0 : ℝ) (SmoothNbhd_zsq hsm) k
    have h' : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (ZR Ψ k p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      simpa only [ZR] using h
    exact h'.lintegral_prod_left'
  -- the `ℝ≥0∞`-chain
  have hmain : ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ))
      ≤ ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (∫ z in Work.Spaces.Iz, PR Ψ k z θ))
          + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (∫ z in Work.Spaces.Iz, ZR Ψ k z θ))) := by
    calc ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (α ^ 2)
            * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ)) := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal C
            * ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
              + ENNReal.ofReal (α ^ 4)
                * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ))) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact key θ hθ
      _ = ENNReal.ofReal C * (∫⁻ θ in Work.Spaces.Iθ,
            ((∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
              + ENNReal.ofReal (α ^ 4)
                * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ)))) := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ,
              ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (PR Ψ k z θ))
            + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ,
              ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (ZR Ψ k z θ))) := by
          rw [MeasureTheory.lintegral_add_left' hPlin,
            MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (α ^ 4)) hZlin]
      _ = ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (∫ z in Work.Spaces.Iz, PR Ψ k z θ))
            + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (∫ z in Work.Spaces.Iz, ZR Ψ k z θ))) := by
          rw [MeasureTheory.lintegral_congr_ae hPeq, MeasureTheory.lintegral_congr_ae hZeq]
  have hbound : ENNReal.ofReal C * ((∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (∫ z in Work.Spaces.Iz, PR Ψ k z θ))
        + ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (∫ z in Work.Spaces.Iz, ZR Ψ k z θ))) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.mpr ⟨hPRlin,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hZRlin⟩)
  have hfinθ : (∫⁻ θ in Work.Spaces.Iθ,
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ)) < ⊤ := by
    have h1 : ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ)) < ⊤ :=
      lt_of_le_of_lt hmain hbound
    rcases ENNReal.mul_lt_top_iff.mp h1 with ⟨-, hb⟩ | h0 | h0
    · exact hb
    · exact absurd h0 (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hα 2)))
    · rw [h0]
      exact ENNReal.zero_lt_top
  -- Tonelli: the `z`-integral of the `θ`-slice integrals is the `θ`-integral of the `z`-ones
  have hswap : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, EXR Ψ k z θ))
      = ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (EXR Ψ k z θ) := by
    have hz_eq : ∀ z ∈ Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, EXR Ψ k z θ)
          = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (EXR Ψ k z θ) := fun z hz =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hEXRsl z hz)
        (Filter.Eventually.of_forall (fun θ => by simp only [EXR]; positivity))
    rw [show (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, EXR Ψ k z θ))
          = ∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (EXR Ψ k z θ) from by
        refine MeasureTheory.lintegral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        exact hz_eq z hz]
    exact MeasureTheory.lintegral_lintegral_swap
      (ENNReal.measurable_ofReal.comp_aemeasurable hEXRaesm.aemeasurable)
  refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp (ne_of_lt ?_)
  · exact hEXRaesm.integral_prod_right'
  · exact Filter.Eventually.of_forall
      (fun z => MeasureTheory.integral_nonneg (fun θ => by simp only [EXR]; positivity))
  · rw [hswap]
    exact hfinθ

end Work.FTS.EllipticEst.TT
