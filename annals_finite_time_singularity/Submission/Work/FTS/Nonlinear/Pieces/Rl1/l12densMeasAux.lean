/-
# `l12densMeasAux` — measurability and integrability tools for the `L₁₂`-densities of `rl1`

The `rl1` row needs, for each of the five groups `N₁, …, N₅` of the paper's nonlinearity `N`,
the `L¹`-integrability on `(0,∞)` of the angular density

  `s ↦ L₁₂dens (N_i α (F_* + g) (Φ_s + Φ_g))(s) = ∫_θ K(θ)·N_i(s,θ)/s dθ`.

Every such statement splits into

* the a.e. strong measurability of the density: the *uncurried* integrand
  `(z,θ) ↦ K(θ)·N_i(z,θ)/z` is a.e.-measurable (it is built out of the blocks of
  `rl1Tools/blockMeas.lean`), and Fubini measurability of the partial integral
  (`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) transports this to the density
  (`aesm_L12dens_of_aem_uncurry`);
* a pointwise bound of the density by an explicit integrable majorant
  (`integrableOn_norm_L12dens_of_le`).

This file supplies both, together with

* the measurability of the derived blocks of the `rl1` rows: the three operators `ℛ, 𝒰, 𝒱` of
  both stream functions `Φ̃_g`, `Φ̃_*`, the three `D`-derivatives of `F = F_* + g`, and the
  angular moment `FK F` (`aem_blocks_gpkg`, `aem_Ftot_blocks`);
* the a.e. strong measurability of the five group densities (`aesm_N1dens`, …,
  `aesm_N5dens`), obtained from the pointwise splits of `N_i` on the open quadrant
  (`Rl1.n2Bound.N2_split`, `Rl1.n3split`, `Rl1.L12densN1Sum.N1_split`) and
  the additivity of `FK` (`L12FK_add_ge0`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.blockMeas
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n2Bound
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n3split
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.L12densN1Sum
import Submission.Work.Coercivity.integral_Itheta_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.Galerkin (Fn)

/-- The product measure of the `rl1` rows: Lebesgue measure on `(0,∞)` times Lebesgue measure
on `Iθ = [0,π/2]`. -/
abbrev rl1Meas : MeasureTheory.Measure (ℝ × ℝ) :=
  Work.FTS.Nonlinear.Pieces.rl1Tools.bmMeasure

/-! ## Generic tools -/

/-- The `rl1` product measure is the planar Lebesgue measure restricted to the open quadrant. -/
theorem rl1Meas_eq_prodRestrict :
    rl1Meas = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
  rw [rl1Meas, Work.FTS.Nonlinear.Pieces.rl1Tools.bmMeasure, MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_congr_set Work.FTS.Nonlinear.Pieces.rl1Tools.ae_prod_eq

/-- Almost every point of the `rl1` product measure has positive first coordinate. -/
theorem ae_fst_pos : ∀ᵐ p ∂rl1Meas, 0 < p.1 := by
  rw [rl1Meas_eq_prodRestrict]
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)]
    with p hp
  exact hp.1

/-- Almost every point of the `rl1` product measure has non-zero first coordinate. -/
theorem ae_fst_ne_zero : ∀ᵐ p ∂rl1Meas, p.1 ≠ 0 :=
  ae_fst_pos.mono fun _ hp => ne_of_gt hp

/-- Almost every point of the `rl1` product measure lies in the open quadrant. -/
theorem ae_mem_Qd : ∀ᵐ p ∂rl1Meas, p ∈ Work.Construction.Qd := by
  rw [rl1Meas_eq_prodRestrict]
  exact MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)

/-- A point of the open quadrant has positive first coordinate, and `z ∈ Ioi (-1)`. -/
theorem mem_Ioi_neg_one_of_mem_Qd {z θ : ℝ} (hq : (z, θ) ∈ Work.Construction.Qd) :
    z ∈ Set.Ioi (-1 : ℝ) := by
  have hz : (0 : ℝ) < z := hq.1
  rw [Set.mem_Ioi]
  linarith

/-- The angular integrand `(z,θ) ↦ K(θ)·f(z,θ)/z` is a.e.-measurable as soon as the uncurried
datum is. -/
theorem aem_uncurry_K_mul_div {f : ℝ → ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry f) rl1Meas) :
    AEMeasurable (Function.uncurry (fun z θ => Work.Spaces.K θ * f z θ / z)) rl1Meas := by
  have hK : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) rl1Meas :=
    (Work.Coercivity.K_facts_continuous.measurable.comp measurable_snd).aemeasurable
  have hinv : AEMeasurable (fun p : ℝ × ℝ => (p.1)⁻¹) rl1Meas :=
    (measurable_inv.comp measurable_fst).aemeasurable
  refine ((hK.mul h).mul hinv).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.uncurry, Pi.mul_apply, div_eq_mul_inv]

/-- A.e. strong measurability of the `L₁₂`-density from a.e.-measurability of the uncurried
datum, by Fubini measurability of the partial integral. -/
theorem aesm_L12dens_of_aem_uncurry {f : ℝ → ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry f) rl1Meas) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens f s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.K θ * f z θ / z)) rl1Meas :=
    (aem_uncurry_K_mul_div h).aestronglyMeasurable
  have h2 := h1.integral_prod_right' (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  show (∫ (y : ℝ), Function.uncurry (fun z θ => Work.Spaces.K θ * f z θ / z) (s, y)
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) = Work.Construction.L12dens f s
  rfl

/-- The norm of the `L₁₂`-density is integrable as soon as it is dominated by an integrable
majorant, the uncurried datum being a.e.-measurable. -/
theorem integrableOn_norm_L12dens_of_le {f : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry f) rl1Meas)
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi (0 : ℝ)))
    (hle : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Construction.L12dens f s‖ ≤ G s) :
    MeasureTheory.IntegrableOn (fun s => ‖Work.Construction.L12dens f s‖)
      (Set.Ioi (0 : ℝ)) :=
  hG.mono' ((aesm_L12dens_of_aem_uncurry h).norm) (hle.mono fun s hs => by
    rwa [Real.norm_of_nonneg (norm_nonneg _)])

/-- An `L¹`-function is integrable once its norm is. -/
theorem integrableOn_of_norm_integrableOn {φ : ℝ → ℝ}
    (haesm : AEStronglyMeasurable φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h : MeasureTheory.IntegrableOn (fun s => ‖φ s‖) (Set.Ioi (0 : ℝ))) :
    MeasureTheory.IntegrableOn φ (Set.Ioi (0 : ℝ)) :=
  (MeasureTheory.integrable_norm_iff haesm).mp h

/-! ## Transfer of a.e.-measurability along the open quadrant -/

/-- Two data agreeing on the open quadrant have a.e. equal uncurried forms for `rl1Meas`. -/
theorem ae_eq_of_forall_mem_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    Function.uncurry f =ᵐ[rl1Meas] Function.uncurry f' :=
  ae_mem_Qd.mono fun p hp => h p.1 p.2 hp

/-- A.e.-measurability of a datum which agrees with an a.e.-measurable datum on the open
quadrant. -/
theorem aem_of_ae_eq_on_Qd {f f' : ℝ → ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry f') rl1Meas)
    (hq : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    AEMeasurable (Function.uncurry f) rl1Meas :=
  h.congr (ae_eq_of_forall_mem_Qd hq).symm

/-- `s2 θ = sin (2θ)` is a.e.-measurable for `rl1Meas`. -/
theorem aem_uncurry_s2 : AEMeasurable (fun p : ℝ × ℝ => Work.Construction.s2 p.2) rl1Meas := by
  have hs : Measurable (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_snd)
  exact hs.aemeasurable

/-- `sin θ ^ 2` is a.e.-measurable for `rl1Meas`. -/
theorem aem_uncurry_sin_sq :
    AEMeasurable (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) rl1Meas := by
  have h : Measurable (fun p : ℝ × ℝ => Real.sin p.2) :=
    Real.measurable_sin.comp measurable_snd
  refine ((h.mul h).aemeasurable).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.mul_apply, pow_two]

/-- `sin(2θ) ≠ 0` on the open angular interval. -/
theorem s2_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  have h1 : 0 < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-- Dividing by `sin(2θ)` does not destroy a.e.-measurability: recovery of the numerator. -/
theorem aem_of_aem_div_s2 {F : ℝ → ℝ → ℝ}
    (h : AEMeasurable (Function.uncurry (fun z θ => F z θ / Work.Construction.s2 θ)) rl1Meas) :
    AEMeasurable (Function.uncurry F) rl1Meas := by
  refine ((aem_uncurry_s2.mul h)).congr ?_
  filter_upwards [ae_mem_Qd] with p hp
  have hne : Work.Construction.s2 p.2 ≠ 0 := s2_ne_zero_of_mem_Ioo hp.2
  simp only [Function.uncurry, Pi.mul_apply]
  exact mul_div_cancel₀ _ hne

/-! ## The derived blocks of the `rl1` rows -/

/-- **Measurability of the elliptic coefficients** of the two stream functions: `ℛ(Φ̃_g)` (given
by `BlockMeas` only after division by `sin 2θ`), `𝒰(Φ̃_g)`, `𝒱(Φ̃_g)`, and
`ℛ(Φ̃_*)`, `𝒰(Φ̃_*)`, `𝒱(Φ̃_*)`. -/
theorem aem_blocks_gpkg {α Ce Cs : ℝ} {g Φs Φg : Fn}
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ)) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ)) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ)) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)) rl1Meas := by
  obtain ⟨-, -, -, -, -, hRg, hUg, hVg, hRs, hUs, hVs, -⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Tools.blockMeas hgal hs hell
  refine ⟨?_, ?_, hVg, hRs, hUs, hVs⟩
  · exact aem_of_aem_div_s2 (F := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) hRg
  · exact aem_of_aem_div_s2 (F := Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg)) hUg

/-- **Measurability of the blocks of the perturbation `g`** and of its angular moment. -/
theorem aem_g_blocks {α : ℝ} {g : Fn} (hgal : Work.FTS.Nonlin.GalClass α g) :
    AEMeasurable (Function.uncurry g) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.pth g)) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dz g)) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dth g)) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ => Work.Construction.FK g z)) rl1Meas := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hcont := Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Qd hg
  exact ⟨Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad hg,
    Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.rl1Tools.sq_pth hg),
    Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.rl1Tools.sq_Dz hg),
    Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.rl1Tools.sq_Dth hg),
    Work.FTS.Nonlinear.Pieces.rl1Tools.fk_aemeasurable hcont⟩

/-- **Measurability of the blocks of the profile `F_*`** and of its angular moment. -/
theorem aem_Fstar_blocks (α : ℝ) :
    AEMeasurable (Function.uncurry (Work.Construction.Fstar α)) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α))) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α))) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dth (Work.Construction.Fstar α))) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.FK (Work.Construction.Fstar α) z)) rl1Meas := by
  have hstar : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hcont := Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Qd hstar
  exact ⟨Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad hstar,
    Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.rl1Tools.sq_pth hstar),
    Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.rl1Tools.sq_Dz hstar),
    Work.FTS.Nonlinear.Pieces.rl1Tools.aem_of_smoothQuad
      (Work.FTS.Nonlinear.Pieces.rl1Tools.sq_Dth hstar),
    Work.FTS.Nonlinear.Pieces.rl1Tools.fk_aemeasurable hcont⟩

/-- **Measurability of the blocks of `F = F_* + g`**: the datum itself, its `θ`-derivative, its
radial derivative, its `D_θ`-derivative, and its angular moment `FK F`. -/
theorem aem_Ftot_blocks {α : ℝ} {g : Fn} (hgal : Work.FTS.Nonlin.GalClass α g) :
    AEMeasurable (Function.uncurry (Work.Construction.Ftot α g)) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.pth (Work.Construction.Ftot α g))) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dz (Work.Construction.Ftot α g))) rl1Meas ∧
    AEMeasurable (Function.uncurry (Work.Spaces.Dth (Work.Construction.Ftot α g))) rl1Meas ∧
    AEMeasurable (Function.uncurry (fun z θ =>
        Work.Construction.FK (Work.Construction.Ftot α g) z)) rl1Meas := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hstar : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hFtot : Work.FTS.LocData.SmoothQuad (Work.Construction.Ftot α g) :=
    Work.FTS.LocData.SmoothQuad_add hstar hg
  obtain ⟨hFm, hFp, hFdz, hFdth, hFKF⟩ := aem_Fstar_blocks α
  obtain ⟨hgm, hpg, hDzg, hDthg, hFKg⟩ := aem_g_blocks hgal
  have hsum_m : AEMeasurable (Function.uncurry (fun z θ =>
      Work.Construction.Fstar α z θ + g z θ)) rl1Meas := by
    refine (hFm.add hgm).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  have hsum_p : AEMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ)) rl1Meas := by
    refine (hFp.add hpg).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  have hsum_dz : AEMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ)) rl1Meas := by
    refine (hFdz.add hDzg).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  have hsum_dth : AEMeasurable (Function.uncurry (fun z θ =>
      Work.Construction.s2 θ * (Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + Work.Spaces.pth g z θ))) rl1Meas := by
    refine (aem_uncurry_s2.mul hsum_p).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.mul_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact aem_of_ae_eq_on_Qd hsum_m fun z θ _ => rfl
  · exact aem_of_ae_eq_on_Qd hsum_p fun z θ hq =>
      Work.FTS.Nonlinear.Pieces.pth_add_of_smoothQuad hstar hg
        (mem_Ioi_neg_one_of_mem_Qd hq) hq.2
  · exact aem_of_ae_eq_on_Qd hsum_dz fun z θ hq =>
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.Nonlinear.Pieces.pz_add_of_smoothQuad hstar hg
          (mem_Ioi_neg_one_of_mem_Qd hq) hq.2)
  · refine aem_of_ae_eq_on_Qd hsum_dth fun z θ hq => ?_
    show Work.Construction.s2 θ * Work.Spaces.pth
      (fun z θ => Work.Construction.Fstar α z θ + g z θ) z θ = _
    rw [Work.FTS.Nonlinear.Pieces.pth_add_of_smoothQuad hstar hg
      (mem_Ioi_neg_one_of_mem_Qd hq) hq.2]
  · exact Work.FTS.Nonlinear.Pieces.rl1Tools.fk_aemeasurable
      (Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Qd hFtot)

/-! ## A.e.-measurability of the uncurried pieces of `N` -/

/-- **The uncurried `N₁` is a.e.-measurable.** -/
theorem aem_N1 {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEMeasurable (Function.uncurry (Work.Construction.N1 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))) rl1Meas := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)).2.1
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z :=
    fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).1 z hz.le
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hg hmem z hz
  refine aem_of_ae_eq_on_Qd (f := Work.Construction.N1 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (f' := fun z θ => Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
      + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ) ?_ ?_
  · obtain ⟨hRg, hUg, hVg, hRs, hUs, hVs⟩ := aem_blocks_gpkg hgal hs hell
    obtain ⟨hgm, hpg, hDzg, hDthg, hFKg⟩ := aem_g_blocks hgal
    obtain ⟨hFm, hFp, hFdz, hFdth, hFKF⟩ := aem_Fstar_blocks α
    have h1 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N1gg α g Φg)) rl1Meas := by
      refine ((hRg.mul hgm).const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N1gg] <;> ring
    have h2 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N1gs α g Φg)) rl1Meas := by
      refine ((hRg.mul hFm).const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N1gs] <;> ring
    have h3 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N1sg α Φs g)) rl1Meas := by
      refine ((hRs.mul hgm).const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N1sg] <;> ring
    have h4 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N1ss α Φs)) rl1Meas := by
      refine ((hRs.mul hFm).const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N1ss] <;> ring
    refine (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  · intro z θ hq
    exact N1_split hα hα1 hg hs.smooth hell.smooth hL hL12 z θ hq

/-- **The uncurried `N₂` is a.e.-measurable.** -/
theorem aem_N2 {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEMeasurable (Function.uncurry (Work.Construction.N2 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))) rl1Meas := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)).2.1
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hg hmem z hz
  refine aem_of_ae_eq_on_Qd (f := Work.Construction.N2 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (f' := fun z θ => Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
      + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ) ?_ ?_
  · obtain ⟨hRg, hUg, hVg, hRs, hUs, hVs⟩ := aem_blocks_gpkg hgal hs hell
    obtain ⟨hgm, hpg, hDzg, hDthg, hFKg⟩ := aem_g_blocks hgal
    obtain ⟨hFm, hFp, hFdz, hFdth, hFKF⟩ := aem_Fstar_blocks α
    have h1 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N2gg α g Φg)) rl1Meas := by
      refine ((hUg.mul hpg).const_mul (-2)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N2gg] <;> ring
    have h2 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N2gs α g Φg)) rl1Meas := by
      refine ((hUg.mul hFp).const_mul (-2)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N2gs] <;> ring
    have h3 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N2sg α Φs g)) rl1Meas := by
      refine ((hUs.mul hpg).const_mul (-2)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N2sg] <;> ring
    have h4 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N2ss α Φs)) rl1Meas := by
      refine ((hUs.mul hFp).const_mul (-2)).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N2ss] <;> ring
    refine (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  · intro z θ hq
    exact N2_split hα hα1 hgal hs.smooth hell.smooth hL12 z θ hq

/-- **The uncurried `N₃` is a.e.-measurable.** -/
theorem aem_N3 {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEMeasurable (Function.uncurry (Work.Construction.N3 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))) rl1Meas := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)).2.1
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z :=
    fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).1 z hz.le
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hg hmem z hz
  refine aem_of_ae_eq_on_Qd (f := Work.Construction.N3 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (f' := fun z θ => Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
      + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ) ?_ ?_
  · obtain ⟨hRg, hUg, hVg, hRs, hUs, hVs⟩ := aem_blocks_gpkg hgal hs hell
    obtain ⟨hgm, hpg, hDzg, hDthg, hFKg⟩ := aem_g_blocks hgal
    obtain ⟨hFm, hFp, hFdz, hFdth, hFKF⟩ := aem_Fstar_blocks α
    have h1 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N3gg α g Φg)) rl1Meas := by
      refine (((hVg.mul hDzg).const_mul (-2)).const_mul α).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N3gg] <;> ring
    have h2 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N3gs α g Φg)) rl1Meas := by
      refine (((hVg.mul hFdz).const_mul (-2)).const_mul α).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N3gs] <;> ring
    have h3 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N3sg α Φs g)) rl1Meas := by
      refine (((hVs.mul hDzg).const_mul (-2)).const_mul α).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N3sg] <;> ring
    have h4 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N3ss α Φs)) rl1Meas := by
      refine (((hVs.mul hFdz).const_mul (-2)).const_mul α).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N3ss] <;> ring
    refine (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  · intro z θ hq
    exact n3split hα hα1 hg hs.smooth hell.smooth hL hL12 z θ hq

/-- **The uncurried `N₄` is a.e.-measurable.** -/
theorem aem_N4 {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEMeasurable (Function.uncurry (Work.Construction.N4 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))) rl1Meas := by
  have hg : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hstar : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  refine aem_of_ae_eq_on_Qd (f := Work.Construction.N4 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (f' := fun z θ => Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
      + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ) ?_ ?_
  · obtain ⟨hgm, hpg, hDzg, hDthg, hFKg⟩ := aem_g_blocks hgal
    obtain ⟨hFm, hFp, hFdz, hFdth, hFKF⟩ := aem_Fstar_blocks α
    have h1 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N4gg α g)) rl1Meas := by
      refine ((hFKg.mul hDthg).const_mul (-(1 / 2))).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N4gg] <;> ring
    have h2 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N4gs α g)) rl1Meas := by
      refine (((hFKg.mul hFp).mul aem_uncurry_s2).const_mul (-(1 / 2))).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N4gs] <;> ring
    have h3 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N4sg α g)) rl1Meas := by
      refine ((hFKF.mul hDthg).const_mul (-(1 / 2))).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N4sg] <;> ring
    have h4 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N4ss α)) rl1Meas := by
      refine (((hFKF.mul hFp).mul aem_uncurry_s2).const_mul (-(1 / 2))).congr
        (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N4ss] <;> ring
    refine (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  · intro z θ hq
    have hz : (0 : ℝ) < z := hq.1
    have hFK : Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z :=
      (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).2 z hz.le
    have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_smoothQuad hstar hg
        (mem_Ioi_neg_one_of_mem_Qd hq) hq.2
    simp only [Work.Construction.N4, Work.FTS.Nonlin.N4gg, Work.FTS.Nonlin.N4gs,
      Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.N4ss, Work.FTS.Nonlinear.Pieces.Dth_eq_s2_mul,
      Work.Construction.Ftot]
    rw [hFK, hpth]
    ring

/-- **The uncurried `N₅` is a.e.-measurable.** -/
theorem aem_N5 {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEMeasurable (Function.uncurry (Work.Construction.N5 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))) rl1Meas := by
  refine aem_of_ae_eq_on_Qd (f := Work.Construction.N5 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (f' := fun z θ => Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
      + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) ?_ ?_
  · obtain ⟨hgm, hpg, hDzg, hDthg, hFKg⟩ := aem_g_blocks hgal
    obtain ⟨hFm, hFp, hFdz, hFdth, hFKF⟩ := aem_Fstar_blocks α
    have hneg : AEMeasurable (fun p : ℝ × ℝ => -(Real.sin p.2 ^ 2)) rl1Meas :=
      aem_uncurry_sin_sq.neg
    have h1 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N5gg g)) rl1Meas := by
      refine ((hneg.mul hFKg).mul hgm).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N5gg] <;> ring
    have h2 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N5gs α g)) rl1Meas := by
      refine ((hneg.mul hFKg).mul hFm).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N5gs] <;> ring
    have h3 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N5sg α g)) rl1Meas := by
      refine ((hneg.mul hFKF).mul hgm).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N5sg] <;> ring
    have h4 : AEMeasurable (Function.uncurry (Work.FTS.Nonlin.N5ss α)) rl1Meas := by
      refine ((hneg.mul hFKF).mul hFm).congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Pi.mul_apply, Work.FTS.Nonlin.N5ss] <;> ring
    refine (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  · intro z θ hq
    have hz : (0 : ℝ) < z := hq.1
    have hFK : Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z :=
      (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).2 z hz.le
    simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
      Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
    rw [hFK]
    ring

/-! ## A.e. strong measurability of the five group densities -/

/-- The density of the `N₁`-group is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_N1dens {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens (Work.Construction.N1 α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aesm_L12dens_of_aem_uncurry (aem_N1 hN hgal hs hell hα hα1 hαα₂)

/-- The density of the `N₂`-group is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_N2dens {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens (Work.Construction.N2 α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aesm_L12dens_of_aem_uncurry (aem_N2 hN hgal hs hell hα hα1 hαα₂)

/-- The density of the `N₃`-group is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_N3dens {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens (Work.Construction.N3 α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aesm_L12dens_of_aem_uncurry (aem_N3 hN hgal hs hell hα hα1 hαα₂)

/-- The density of the `N₄`-group is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_N4dens {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens (Work.Construction.N4 α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aesm_L12dens_of_aem_uncurry (aem_N4 hN hgal hs hell hα hα1 hαα₂)

/-- The density of the `N₅`-group is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_N5dens {α₂ Ci Ce Cs α : ℝ} {g Φs Φg : Fn} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hgal : Work.FTS.Nonlin.GalClass α g) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂) :
    AEStronglyMeasurable (fun s => Work.Construction.L12dens (Work.Construction.N5 α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  aesm_L12dens_of_aem_uncurry (aem_N5 hN hgal hs hell hα hα1 hαα₂)

end Work.FTS.Nonlinear.Pieces.Rl1
