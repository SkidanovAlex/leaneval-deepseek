/-
# `Work.FTS.GalFields.Norm.Xn_LGammaT_le` — the `ℋ⁴`-norm of `𝓛_Γ^T g` against the `ℋ⁵`-norm

The lemma is the `L1` row of the `RHSData` plan (`FTS/GalFields/NOTES_RHSData.md`): the linear
part `𝓛_Γ^T` of the dynamic right-hand side satisfies

  `|𝓛_Γ^T g|_{ℋ⁴} ≤ K · |g|_{ℋ⁵}`

with a constant `K` **independent of `α`** (the `ℋ⁵`-size of `g` is the largest norm the
interface `RHSData` allows).

## Route

`𝓛_Γ^T = 𝓛̂ + Corr` (`Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr`), and the two summands
are handled separately.

* the clean part `𝓛̂ = 𝓛 − Transport` is handled by the pointwise integrand domination
  `StrongPersist.H6Aux.Lhat_integrand_le` at level four: `HkSq α 4 (𝓛̂g) ≤ C·HkSq α 5 g`, with a
  constant free of `α` (the proof's constant is `8·(zmulConst 4·(1+K)²) + 9`; the only `α`-input
  is `α > 0`, through the index shift `HkIntegrand α 4 (D_θg) ≤ HkIntegrand α 5 g`);
* the correction `Corr α g = Γ(θ)·radA α g z` (`Transfer.Corr_eq_radA`) is a *separated* product
  of the angular profile `Γ(θ) = (sinθ cos²θ)^{α/3}` and a `z`-only profile, so the pointwise
  separation `E2norm.HkIntegrand_ang_rad_le_n` at `n = 4` gives

    `HkIntegrand α 4 (Corr α g) z θ
       ≤ (Σ_{j<5}(D_z^j radA α g)²w²) · (smE θ + 4·(10⁵α)²·sin(2θ)^{2α/5-γ}θ)`.

  The `θ`-integral of the angular factor is bounded uniformly in `α`
  (the `(4·10¹⁰α²)` coefficient times `1000/(3α)` plus the light weight's `10⁴`
  give `≤ 2·10¹³`, `ang_fac_integrable_bound`), and the `z`-integral of the radial slot sum by
  `C·(HkSq α 4 g + HkSq α 4 (D_θg))` (`radA_slotSum4_le`), whence
  `HkSq α 4 (Corr α g) ≤ K·HkSq α 4 g`.

The two integrated bounds are combined with `E2norm.HkSq_add_le` and
`OpenPkg.HkMem_add_of_contDiffOn_four` after `𝓛_Γ^T = 𝓛̂ + Corr`, and the square root is taken at
the end (`Xn = √HkSq`, `√(a·b) = √a·√b`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.HkIntegrand_ang_rad_le_n
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.gam_rad_integral_le
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.Pieces
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.FTS.OpenPkg.AprioriOpen.Bound
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.GalFields.Norm.radA_slotSum4_le
import Submission.Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four
import Submission.Work.FTS.GalFields.Norm.ang_fac_integrable_bound
import Submission.Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two one-dimensional objects of the separated product -/

/-- The level-four radial slot sum `Σ_{j<5}(D_z^j B)²w²` of a `z`-only profile `B`. -/
def slot5 (B : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, (Work.Elliptic.DzdIter j B z) ^ 2 * (Work.Spaces.w z) ^ 2

theorem slot5_nonneg (B : ℝ → ℝ) (z : ℝ) : 0 ≤ slot5 B z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The angular factor of the level-four separated product `Γ(θ)·r(z)`: the light weight
`smE θ = sin(2θ)^{-η}` plus the heavy slot with the sharp `α²`-coefficient and the combined
exponent `2α/5 - γ = 3α/10 - 1 ∈ (-1,0)`. -/
def afac4 (α : ℝ) (θ : ℝ) : ℝ :=
  Work.FTS.Nonlinear.RadialProd.smE θ
    + 4 * (100000 * α) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)

/-! ## The pointwise separation of `Corr α g = Γ(θ)·radA α g z` -/

/-- **The pointwise `ℋ⁴`-integrand bound for the transfer correction.**  For `θ ∈ Iθ` the
`ℋ⁴`-integrand of `Corr α g = Γ(θ)·radA α g z` is dominated by the product of the level-four
radial slot sum of `radA α g` and the angular factor `afac4 α`.

Proof: `E2norm.HkIntegrand_ang_rad_le_n` at `n = 4`, with angular profile `a = Γ`, `B0 = 1`
(`Γ ≤ 1`), `B1 = 10⁵α`, `G θ = sin(2θ)^{α/5}`: `|D_θ^iΓ| ≤ 10⁵α·Γ` for `1 ≤ i ≤ 4`
(`E2norm.DthIter_Gam_abs_le_alpha`) and `Γ ≤ sin(2θ)^{α/5}` (`LocData.Gam_le_sin_two_rpow`);
the heavy slot is then folded with `(sin(2θ)^{α/5})²·smG = sin(2θ)^{2α/5-γ}`
(`E2norm.rpow_sq_smG_eq`). -/
theorem HkIntegrand_Corr_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (g : Fn) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α g) z θ
      ≤ slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ := by
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ (1 : ℝ) := fun θ hθ => by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rwa [abs_of_nonneg h1]
  have hB1pos : (0 : ℝ) < 100000 * α := by positivity
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (100000 * α) * (fun θ' => (Real.sin (2 * θ')) ^ (α / 5)) θ := by
    intro i hi hi4 θ hθ
    refine (Work.FTS.CoercivityFix.Transfer.E2norm.DthIter_Gam_abs_le_alpha i hi hi4 α hα
      hα1 hθ).trans ?_
    exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ) hB1pos.le
  have hfun : Work.FTS.CoercivityFix.Corr α g
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α g z := by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α g z θ
  rw [hfun]
  have hsep := Work.FTS.CoercivityFix.Transfer.E2norm.HkIntegrand_ang_rad_le_n (n := 4) (le_refl 4)
    (α := α) (a := fun θ => Work.Spaces.Gam α θ)
    (r := fun z => Work.FTS.CoercivityFix.Transfer.radA α g z)
    (G := fun θ => (Real.sin (2 * θ)) ^ (α / 5)) (B0 := 1) (B1 := 100000 * α)
    (z := z) (θ := θ) ha0 ha1 hθ
  refine hsep.trans (le_of_eq ?_)
  have hang : (1 : ℝ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + 4 * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ = afac4 α θ := by
    rw [one_pow, one_mul]
    rw [show (4 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ
        = 4 * (100000 * α) ^ 2
          * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        from by ring]
    rw [Work.FTS.CoercivityFix.Transfer.E2norm.rpow_sq_smG_eq α hα hα1 hθ]
    rfl
  rw [hang]
  rfl

/-! ## The `ℋ⁴`-bound for the transfer correction -/

/-- **The `ℋ⁴`-membership and norm bound of `Corr α g`.**  From the pointwise separation, the
`α`-uniform angular integral bound `hang` and the level-four radial slot bound `hrad`, both the
honesty of `Corr α g` (via `HkMem_of_majorant`, whose continuity hypothesis is the level-four
smoothness `hsm` of `Corr`) and the squared norm bound follow, with `K = Kang·Crad`. -/
theorem HkSq_Corr_le {Kang Crad : ℝ} (hKang : 0 < Kang) (hCrad : 0 < Crad)
    (hang : ∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (fun θ => afac4 α θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, afac4 α θ) ≤ Kang)
    (hrad : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.CoerAdm α f → Work.Spaces.HkMem α 4 f →
        MeasureTheory.IntegrableOn
          (fun z : ℝ => slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          ≤ Crad * (Work.Spaces.HkSq α 4 f + Work.Spaces.HkSq α 4 (Work.Spaces.Dth f)))
    (hsm : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 5 g →
        ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α g))
          Work.FTS.EllipticEst.Q0)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Fn}
    (hCoer : Work.FTS.Nonlin.CoerAdm α g) (h4 : Work.Spaces.HkMem α 4 g) :
    Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Corr α g) ∧
      Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α g)
        ≤ Kang * Crad * (Work.Spaces.HkSq α 4 g + Work.Spaces.HkSq α 4 (Work.Spaces.Dth g)) := by
  have h5 : Work.Spaces.HkMem α 5 g := hCoer.reg.2.1
  have hsmG : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hCoer.reg.1
  obtain ⟨hCint, hCbd⟩ := hang α hα hα1
  obtain ⟨hradInt, hradBd⟩ := hrad α hα hα1 g hCoer h4
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α g) z θ
        ≤ slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ :=
    fun z _ θ hθ => HkIntegrand_Corr_le hα hα1 g hθ
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn
        (fun θ => slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ)
        Work.Spaces.Iθ := by
    intro z _
    exact hCint.const_mul (slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z)
  refine ⟨?_, ?_⟩
  · -- the honesty of `Corr α g`
    refine Work.FTS.LocData.HkMem_of_majorant α 4
      (f := Work.FTS.CoercivityFix.Corr α g)
      (M := fun z θ => slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ)
      ?_ ?_ ?_ ?_
    · exact Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (n := 4) (k := 4) α le_rfl
        (hsm α hα hα1 g hsmG h5)
    · exact hMslice
    · have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
            slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ)
          = fun z => slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z
              * (∫ θ in Work.Spaces.Iθ, afac4 α θ) := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact hradInt.mul_const _
    · exact hpt
  · -- the squared norm bound
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Work.FTS.CoercivityFix.Corr α g) z θ)
          ≤ slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * Kang := by
      intro z hz
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Work.FTS.CoercivityFix.Corr α g) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
          (hMslice z hz)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => hpt z hz θ hθ))
      rw [MeasureTheory.integral_const_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hCbd (slot5_nonneg _ z))
    have hInt : MeasureTheory.IntegrableOn
        (fun z => slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * Kang)
        Work.Spaces.Iz :=
      hradInt.mul_const Kang
    have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (Work.FTS.CoercivityFix.Corr α g) z θ)
        ≤ Kang * (∫ z in Work.Spaces.Iz,
            slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z) := by
      have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Work.FTS.CoercivityFix.Corr α g) z θ)
          ≤ ∫ z in Work.Spaces.Iz,
              slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * Kang :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
          hInt
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => hinner z hz))
      have h2 : (∫ z in Work.Spaces.Iz,
            slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * Kang)
          = Kang * (∫ z in Work.Spaces.Iz,
              slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z) := by
        rw [MeasureTheory.integral_mul_const]
        ring
      rwa [h2] at h1
    calc Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Work.FTS.CoercivityFix.Corr α g) z θ := rfl
      _ ≤ Kang * (∫ z in Work.Spaces.Iz,
            slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z) := houter
      _ ≤ Kang * (Crad * (Work.Spaces.HkSq α 4 g + Work.Spaces.HkSq α 4 (Work.Spaces.Dth g))) :=
          mul_le_mul_of_nonneg_left hradBd hKang.le
      _ = Kang * Crad * (Work.Spaces.HkSq α 4 g + Work.Spaces.HkSq α 4 (Work.Spaces.Dth g)) := by
          ring

/-! ## The main theorem -/

theorem Xn_LGammaT_le {α₂ Ci Ct Ce Cs : ℝ} {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α g) ∧
      Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α g) ≤ K * Work.FTS.GalFields.Xn5 α g := by
  obtain ⟨Cl, hClpos, hL⟩ := HkSq_Lhat_le_uniform
  obtain ⟨Kang, hKangpos, hang⟩ := ang_fac_integrable_bound
  obtain ⟨Crad, hCradpos, hrad⟩ := radA_slotSum4_le
  refine ⟨Real.sqrt (2 * Cl + 4 * (Kang * Crad)) + 1, by positivity, ?_⟩
  intro α g hα hα1 hαα₂ hgal
  have hsmG : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1
  have h6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have h5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsmG h6
  have h4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsmG h6
  have hCoer : Work.FTS.Nonlin.CoerAdm α g :=
    Work.FTS.OpenPkg.AprioriOpen.coerAdm_of_galClass hgal
  -- the two summands of `𝓛_Γ^T = 𝓛̂ + Corr`
  have hLhat_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat g) :=
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα 4 hsmG h5
  have hLhat_bd : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g)
      ≤ Cl * Work.Spaces.HkSq α 5 g := hL α hα g hsmG h5
  have hLhat_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Lhat g))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hsmG).forall 4
  obtain ⟨hCorr_mem, hCorr_bd⟩ := HkSq_Corr_le hKangpos hCradpos hang hrad
    (fun α hα hα1 g hsm h5 => (radA_Corr_contDiffOn_four hα hα1 hsm h5).2)
    hα hα1 hCoer h4
  have hCorr_sm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α g))
      Work.FTS.EllipticEst.Q0 :=
    (radA_Corr_contDiffOn_four hα hα1 hsmG h5).2
  have hLGT_mem : Work.Spaces.HkMem α 4 (Work.FTS.CoercivityFix.Lhat g
      + Work.FTS.CoercivityFix.Corr α g) :=
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hLhat_sm hCorr_sm hLhat_mem hCorr_mem
  have hpt_add : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Lhat g
          + Work.FTS.CoercivityFix.Corr α g) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Lhat g) z θ
          + 2 * Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α g) z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 4
      (f := Work.FTS.CoercivityFix.Lhat g) (g := Work.FTS.CoercivityFix.Corr α g)
      hLhat_sm hCorr_sm
  have hsum : Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g
        + Work.FTS.CoercivityFix.Corr α g)
      ≤ 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g)
        + 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α g) :=
    Work.FTS.CoercivityFix.Transfer.E2norm.HkSq_add_le α 4 hLhat_mem hCorr_mem hLGT_mem hpt_add
  have hmono4 : Work.Spaces.HkSq α 4 g ≤ Work.Spaces.HkSq α 5 g :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) h5
  have hdth : Work.Spaces.HkSq α 4 (Work.Spaces.Dth g) ≤ Work.Spaces.HkSq α 5 g :=
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 4 h5
  have hbd : Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α g)
      ≤ (2 * Cl + 4 * (Kang * Crad)) * Work.Spaces.HkSq α 5 g := by
    have hLGTeq : Work.Coercivity.LGammaT α g
        = Work.FTS.CoercivityFix.Lhat g + Work.FTS.CoercivityFix.Corr α g :=
      Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α g
    rw [hLGTeq]
    have h2 : 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α g)
        ≤ 2 * (Kang * Crad) * (Work.Spaces.HkSq α 5 g + Work.Spaces.HkSq α 5 g) := by
      have h3 : Work.Spaces.HkSq α 4 g + Work.Spaces.HkSq α 4 (Work.Spaces.Dth g)
          ≤ Work.Spaces.HkSq α 5 g + Work.Spaces.HkSq α 5 g := add_le_add hmono4 hdth
      have hKC : 0 ≤ Kang * Crad := mul_nonneg hKangpos.le hCradpos.le
      calc 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α g)
          ≤ 2 * (Kang * Crad * (Work.Spaces.HkSq α 4 g
              + Work.Spaces.HkSq α 4 (Work.Spaces.Dth g))) :=
            mul_le_mul_of_nonneg_left hCorr_bd (by norm_num)
        _ = 2 * (Kang * Crad) * (Work.Spaces.HkSq α 4 g
              + Work.Spaces.HkSq α 4 (Work.Spaces.Dth g)) := by ring
        _ ≤ 2 * (Kang * Crad) * (Work.Spaces.HkSq α 5 g + Work.Spaces.HkSq α 5 g) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5nn : 0 ≤ Work.Spaces.HkSq α 5 g := Work.Spaces.HkSq_nonneg α 5 g
    calc Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g
            + Work.FTS.CoercivityFix.Corr α g)
        ≤ 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g)
          + 2 * Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Corr α g) := hsum
      _ ≤ 2 * (Cl * Work.Spaces.HkSq α 5 g)
          + 2 * (Kang * Crad) * (Work.Spaces.HkSq α 5 g + Work.Spaces.HkSq α 5 g) :=
          add_le_add (mul_le_mul_of_nonneg_left hLhat_bd (by norm_num)) h2
      _ ≤ (2 * Cl + 4 * (Kang * Crad)) * Work.Spaces.HkSq α 5 g := by
          nlinarith [h5nn, hClpos.le, hKangpos.le, hCradpos.le]
  refine ⟨?_, ?_⟩
  · rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α g]
    exact hLGT_mem
  · have hK2 : 0 ≤ 2 * Cl + 4 * (Kang * Crad) := by positivity
    have hXg : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
    calc Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α g)
        = Real.sqrt (Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α g)) := rfl
      _ ≤ Real.sqrt ((2 * Cl + 4 * (Kang * Crad)) * Work.Spaces.HkSq α 5 g) :=
          Real.sqrt_le_sqrt hbd
      _ = Real.sqrt (2 * Cl + 4 * (Kang * Crad)) * Work.FTS.GalFields.Xn5 α g := by
          rw [Real.sqrt_mul hK2]
          rfl
      _ ≤ (Real.sqrt (2 * Cl + 4 * (Kang * Crad)) + 1) * Work.FTS.GalFields.Xn5 α g :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXg

end Work.FTS.GalFields.Norm
