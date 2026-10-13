import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_integral_eq_neg_limit
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2
import Submission.Work.FTS.EllipticEst.Endpt.moment_chain_pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- `θ ↦ sinθcos²θ` is continuous. -/
theorem endpt_continuous_sinCos2 : Continuous (fun θ : ℝ => sg θ) := by
  simp only [Work.Elliptic.sinCos2]
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `θ ↦ |sinθcos²θ|` is integrable on `Iθ`. -/
theorem endpt_integrableOn_abs_sinCos2 :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) Iθ := by
  have h : MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) (Set.Icc 0 (π / 2)) :=
    (endpt_continuous_sinCos2.abs.continuousOn).integrableOn_compact isCompact_Icc
  rw [Work.Spaces.Iθ]
  exact h

/-- Slice integrability of `θ ↦ Ψ z θ · sinθcos²θ` from the boundedness of the slice. -/
theorem endpt_slice_mul_sinCos2_integrable {Ψ : ℝ → ℝ → ℝ} {z C : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hz : 0 < z) (hC : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |Ψ z θ| ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Ψ z θ * sg θ) Iθ := by
  have hS : SmoothOpen Ψ := smoothOpen_of_forall hsm
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => Ψ z θ * sg θ)
      (MeasureTheory.volume.restrict Iθ) :=
    (Work.FTS.EllipticEst.remov.ws_aesm_slice hS hz).mul
      endpt_continuous_sinCos2.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono'
    (endpt_integrableOn_abs_sinCos2.const_mul C) haesm ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC θ hθ) (abs_nonneg _)

/-- Slice integrability of `θ ↦ g z θ · sinθcos²θ` from `HkMem α 0 g`. -/
theorem endpt_slice_mul_sinCos2_integrable_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hg : SmoothOpen g) (hmem : Work.Spaces.HkMem α 0 g) (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => g z θ * sg θ) Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Iθ := by
    have h0 := hmem.1 z hzI
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [Work.Spaces.HkIntegrand]
  have hC1 : (1 : ℝ) ≤ (z ^ 2)⁻¹ + 1 := by
    have : 0 < (z ^ 2)⁻¹ := by positivity
    linarith
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ => ((z ^ 2)⁻¹ + 1)
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
      Iθ :=
    (hGint.const_mul _).add (MeasureTheory.integrableOn_const
      (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
  refine MeasureTheory.Integrable.mono' hmaj
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice hg hz).mul
      endpt_continuous_sinCos2.aestronglyMeasurable) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted (f := fun θ => g z θ) hz hθI
  rw [abs_mul] at h1
  rw [Real.norm_eq_abs, abs_mul]
  have hX : 0 ≤ (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    sq_nonneg _
  have h2 : (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ((z ^ 2)⁻¹ + 1)
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hC1 hX
  linarith [h1, h2]

/-- **The moment identity for `F`.**  From `bslOp α Ψ = F` on the open quadrant and the
integrability of the three summands, the moment of `F` is the combination of the moments of
`∂_zΨ`, `∂_z²Ψ` and `Lzero1 (Ψ z ·)`. -/
theorem endpt_fstar_F_moment {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hEq : ∀ θ : ℝ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz Ψ z θ * sg θ) Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sg θ) Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) Iθ) :
    Work.Elliptic.Fstar F z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z
        + ∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ := by
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ => -(α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ)) Iθ := h2.const_mul _
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ => -(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ)) Iθ := h1.const_mul _
  have hcongr : (∫ θ in Iθ, F z θ * sg θ)
      = ∫ θ in Iθ, (-(α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ)
          + (-(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ)
            + Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [← hEq θ hθ.1 hθ.2, Work.Elliptic.bslOp_apply,
      show Work.Elliptic.Lzero Ψ z θ
        = Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ from rfl]
    ring
  rw [Work.Elliptic.Fstar, hcongr]
  rw [MeasureTheory.integral_add
    (f := fun θ => -(α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ))
    (g := fun θ => -(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ)
      + Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) hI1 (hI2.add h3)]
  rw [MeasureTheory.integral_add
    (f := fun θ => -(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ))
    (g := fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) hI2 h3]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [Work.Elliptic.Fstar]
  ring

/-- **The `θ = 0` endpoint limit of the slices vanishes (a.e. in `z`).**

This is the "endpoint bootstrap" step of the weak-class level-`0` estimate
(`Work.FTS.EllipticEst.l2etaWeakFts`, `Work.FTS.EllipticEst.L2EtaHonestCore`): the Dirichlet
data of the target are *values* (`Ψ z 0 = 0`), while the integrals only see the open quadrant —
so a datum could in principle have a *jump* at `θ = 0` (its slice tending to `A(z) ≠ 0`).  The
two solvability conditions exclude that.

## Proof

Write `s θ := Work.Elliptic.sinCos2 θ = sinθ cos²θ` (`s(0) = 0`, `s'(0) = 1`, `s(π/2) = s'(π/2) = 0`)
and `A(z) := lim_{θ→0⁺}Ψ(z,θ)`, which exists for every `z > 0`:
`hmB` gives `(∂_θθΨ(z,·))² sin(2θ)^{-η} ∈ L¹(Iθ)`, hence `∂_θθΨ(z,·) ∈ L¹`, and the FTC on
`(0,a]` makes `Ψ(z,·)` and `∂_θΨ(z,·)` converge at `0⁺` (they are bounded by `|∂_θθ|`-integrals
plus a base value).  The same FTC gives the IBP

  `∫_θ (Lzero (Ψ z ·)) θ · s θ = [Ψ s' − Ψ' s + tanθ·Ψ·s]_0^{π/2} + ∫_θ Ψ·LzeroAdj(s) = −A(z)`

(`Work.Elliptic.LzeroAdj_sinCos2` says `LzeroAdj s = 0`; the boundary term at `π/2` vanishes
because `s = s' = 0` there and `tanθ·Ψ·s → 0`; at `0` only `Ψ·s'` survives, with `s'(0) = 1`;
see `Work.Elliptic.Defs` for `Lzero`, `LzeroAdj`, and `Work.FTS.EllipticEst.SliceAux` /
`Auxiliary/Lzero_self_form_fts` for the pattern of such an IBP).

Pointwise on the open quadrant `bslOp α Ψ = −α²z²∂_zzΨ − α(5+α)z∂_zΨ + Lzero Ψ`, so with
`hEq` and `hOF` (`∫_θ F(z,·)s = 0` for every `z`):

  `0 = ∫_θ F(z,·)s = −α²z²∫_θ (∂_zzΨ)(z,·)s − α(5+α)z∫_θ (∂_zΨ)(z,·)s − A(z)`.

Finally `hOP` says the moment `Ψ_*(z) := ∫_θ Ψ(z,θ)s(θ)dθ` is *identically zero*, so its first
two `z`-derivatives vanish; by differentiation under the integral sign the two integrals above
are those derivatives for a.e. `z` — this is where the joint-integrability hypotheses
`hmU : HkMem α 0 (z ∂_zΨ)` and `hmZ : HkMem α 0 (z²∂_zzΨ)` enter (they give, via Tonelli, that
`(z,θ) ↦ s θ · ∂_z^jΨ z θ` is jointly integrable on a full-measure set of `z`; `hmU` is itself
derivable from `hmZ` by the radial Agmon/Hardy interpolation, cf.
`Submission.Work.FTS.EllipticEst.AngSecond.radialDzInterp` and
`Work.FTS.EllipticEst.HkNorm_Dz_le_open`).  Hence `A(z) = 0` for a.e. `z`. -/
theorem l2etaEndpointZeroLeft (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (h0 : ∀ z, Ψ z 0 = 0) (h1 : ∀ z, Ψ z (π / 2) = 0)
    (hOF : Work.Elliptic.OrthCond F) (hOP : Work.Elliptic.OrthCond Ψ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hmU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hslice : ∀ z : ℝ, 0 < z → ∀ n : ℕ,
      ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    fun z hz n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n
  have hSΨ : SmoothOpen Ψ := smoothOpen_of_forall hsm
  -- ## the two slice-integrability inputs of the moment chain
  have hψsl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Ψ z θ * sg θ) Iθ := by
    intro z hz
    obtain ⟨C, -, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmB hz
    exact endpt_slice_mul_sinCos2_integrable hsm hz (fun θ hθ => (hC θ hθ).1)
  have hp1sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * sg θ) Iθ := by
    intro z hz
    have hSg : SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
      contDiff_fst.contDiffOn.mul hSΨ.pz
    have h := endpt_slice_mul_sinCos2_integrable_of_HkMem (g := _) hSg hmU hz
    refine (h.const_mul z⁻¹).congr (Filter.Eventually.of_forall (fun θ => ?_))
    show z⁻¹ * ((z * Work.Spaces.pz Ψ z θ) * sg θ) = Work.Spaces.pz Ψ z θ * sg θ
    rw [← mul_assoc z⁻¹ (z * Work.Spaces.pz Ψ z θ) (sg θ),
      ← mul_assoc z⁻¹ z (Work.Spaces.pz Ψ z θ), inv_mul_cancel₀ (ne_of_gt hz), one_mul]
  have hp2sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sg θ) Iθ := by
    intro z hz
    have hSg : SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      (contDiff_fst.pow 2).contDiffOn.mul (hSΨ.pzIter 2)
    have h := endpt_slice_mul_sinCos2_integrable_of_HkMem (g := _) hSg hmZ hz
    refine (h.const_mul ((z ^ 2)⁻¹)).congr (Filter.Eventually.of_forall (fun θ => ?_))
    show (z ^ 2)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ)
      = Work.Spaces.pzIter 2 Ψ z θ * sg θ
    rw [← mul_assoc (z ^ 2)⁻¹ (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (sg θ),
      ← mul_assoc (z ^ 2)⁻¹ (z ^ 2) (Work.Spaces.pzIter 2 Ψ z θ),
      inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hz)), one_mul]
  -- ## the moment chain
  obtain ⟨hT1zero, hT2ae⟩ := Work.FTS.EllipticEst.Endpt.moment_chain_pz hsm hOP
    (Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi hsm hmU)
    (Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi hsm hmZ)
    hψsl hp1sl (Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 hsm hmZ)
  -- ## the endpoint argument, for a.e. `z`
  filter_upwards [hT2ae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hT2z hz
  obtain ⟨C, -, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmB hz
  have h2slice : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := Ψ) hmB hz
    refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 Ψ z θ
      = deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ from rfl]
  have hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) Iθ :=
    Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable hsm hmB hz hC
  obtain ⟨a, ha⟩ := sliceLimitLeftExists (fun θ => Ψ z θ) (hslice z hz) h2slice
  have hIBP : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) = -a :=
    Work.FTS.EllipticEst.Endpt.Lzero1_integral_eq_neg_limit (hslice z hz 2) h2slice hL ha
  have hFmom := endpt_fstar_F_moment (z := z)
    (fun θ hθ1 hθ2 => hEq z hz θ hθ1 hθ2) (hp1sl z hz) (hp2sl z hz) hL
  have ha0 : a = 0 := by
    rw [hOF z, hT1zero z hz, hT2z, hIBP] at hFmom
    ring_nf at hFmom
    linarith [hFmom]
  simpa [ha0] using ha

end Work.FTS.EllipticEst
