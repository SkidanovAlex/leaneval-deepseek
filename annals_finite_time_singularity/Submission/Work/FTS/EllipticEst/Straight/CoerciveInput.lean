/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Straight.coercive_input`: the a-priori `ℋ^k` input for the straightened solution

**Provenance (read this first).**  This file is a verbatim copy of
`Submission/Work/Blocks/straight_Hk_input_clean.lean` (`Work.Blocks.straight_Hk_input_clean`),
whose *proof* is unchanged, with exactly three mechanical changes:

* the import of `Submission.Work.FTS.EllipticEst.EllHyp_certificates` is replaced by its
  clash-free shim `Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates`, and
  `Cert.HkMem_pthIter2_EllResid` by `TT.Shim.HkMem_pthIter2_EllResid` (the originals cannot be
  loaded together with `OpenQDefs`: both declare
  `Work.FTS.EllipticEst.integrableOn_zSummand`) -- without these substitutions the source file
  does not elaborate at all;
* the namespace `Work.Blocks` became `Work.FTS.EllipticEst.Straight`;
* the theorem `straight_Hk_input_clean` was renamed `coercive_input`.

Its purpose is to provide, in a clash-free cone, the `ℋ^k`-input consumed by
`Work.FTS.EllipticEst.Straight_DzHk_le` (whose assignment-path provider
`Submission/Work/FTS/EllipticEst/Straight_Hk_input.lean` is still a bare placeholder).
Verified `#print axioms Work.FTS.EllipticEst.Straight.coercive_input`
`= [propext, Classical.choice, Quot.sound]`.

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals of Math. **194** (2021), §'Elliptic Regularity Estimates'.

For the data `(F, Ψ)` of the class `EllHyp α k F Ψ` (`k ≥ 2`, `0 < α ≤ 1/4`) for which the
*straightened* solution

  `V = Ψ + Gsing α F · sin 2θ`

satisfies the orthogonality condition `OrthCond V` (i.e. `V_* = ∫_θ V sinθcos²θ dθ ≡ 0`), we
prove

* `V ∈ ℋ^k` and `z²∂_zzV ∈ ℋ^k` (the two membership conjuncts), and
* the a-priori estimate
  `|V|_{ℋ^k} ≤ C (|F|_{ℋ^k} + |∂_θθV|_{ℋ^k} + α²|z²∂_zzΨ|_{ℋ^k})`, `C` independent of `α, F, Ψ`.

## The route

1. **(Moment form.)**  The orthogonality condition says `F_*(V) ≡ 0`; splitting
   `F_*(V) = F_*(Ψ) + Gsing α F · ∫_θ sin 2θ · sinθcos²θ dθ = F_*(Ψ) + (4/15) Gsing α F`
   (`Fstar_Vf_split`) gives, *for every* `z > -1`,

     `Gsing α F z = -(15/4)·F_*(Ψ)(z)`   (`Gsing_eq_moment`),

   so on the open quadrant `V` coincides with the explicit function

     `W = Ψ - (15/4)·F_*(Ψ)·sin 2θ`      (`Vf_eq_Wf`).

   This removes the singular term `Gstar = -(1/4α)L₁₂(F)` from the problem: `W` only involves
   the angular moment of the *smooth* function `Ψ`.

2. **(Memberships.)**  Since `Ψ` is `SmoothNbhd` (analytic), `F_*(Ψ)` is analytic on `(0,∞)`
   (`analytic_fstar_radial`, from the parametric-integral theorem
   `Coercivity.contDiffOn_setIntegral_Itheta`), hence `W` is `SmoothHalf`
   (`SmoothHalf_Wf`); the membership `W ∈ ℋ^k` follows from `HkMem α k Ψ` and the
   moment-membership `F_*(Ψ)·sin 2θ ∈ ℋ^k` (`Cert.HkMem_Fstar_sin_open`).  Transfers along the
   open quadrant (`HkMem_agreeOnQ`, `HkSq_congr_open`) turn this into the memberships of `V`.

   For `∂_θθV = ∂_θθΨ + 15·F_*(Ψ)·sin 2θ` (`HkMem_pthIter2_Vf`) and for `z²∂_zzV` we use the
   *straightening identities* `alphaDzIter2_straight_eq`, `alphaDz_straight_eq` together with
   `D_z²f = z²∂_zzf + D_zf`: they give, on the open quadrant,

     `α² z²∂_zz V = α²z²∂_zzΨ + (15/4)·F_*(F)·sin 2θ + (25+5α)·Ḡ α F·sin 2θ`,

   whose memberships are `HkMem α k (z²∂_zzΨ)` (`EllHyp.memZ2`), `Cert.FstarSin_layer` and
   `Cert.HkMem_Gbar_sin`.

3. **(The estimate.)**  `Blocks.poincare_Half` (the slicewise angular coercivity in the
   half-strip class `SmoothHalf`, `poincare_Half`) gives `|W|_{ℋ^k} ≤ C|∂_θθW|_{ℋ^k}` for every
   `SmoothHalf` function vanishing on the two angular boundary lines.  `W` is such a function
   (`SmoothHalf_Wf`, `VanishTheta_Wf`) and `∂_θθW = ∂_θθV` on the open quadrant, so
   `|V| = |W| ≤ C|∂_θθV| ≤ C(|F| + |∂_θθV| + α²|z²∂_zzΨ|)` by the positivity of the remaining
   terms.

   Note that the stronger class `SmoothNbhd` (analyticity on a neighbourhood of the *closed*
   quadrant, needed by `Blocks.theta_Hk_poincare`) is *not* available here: `F_*(Ψ)` is defined
   by an integral over `(0,∞)` and carries no information for `z < 0`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_layer
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin
import Submission.Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar
import Submission.Work.FTS.EllipticEst.TT.Straight_certs
import Submission.Work.FTS.EllipticEst.HalfSmooth
import Submission.Work.Coercivity.contDiffOn_setIntegral_Itheta
import Submission.Work.Blocks.poincare_Half
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Straight

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The straightened solution and its moment form -/

/-- The straightened solution `V = Ψ + Gsing α F · sin 2θ`. -/
def Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

/-- The explicit moment form `W = Ψ - (15/4)·F_*(Ψ)·sin 2θ` of the straightened solution.  On
the open quadrant `W` agrees with `V` whenever the orthogonality condition holds
(`Vf_eq_Wf`). -/
def Wf (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + (-(15 / 4)) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))

/-- **The angular moment splits over the `sin 2θ` direction**:
`F_*(Ψ + G·sin 2θ) = F_*(Ψ) + G·(4/15)`. -/
lemma Fstar_Vf_split (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : -1 < z) :
    Work.Elliptic.Fstar (Vf α F Ψ) z
      = Work.Elliptic.Fstar Ψ z + Work.Elliptic.Gsing α F z * (4 / 15) := by
  have hslice : ContinuousOn (fun θ : ℝ => Ψ z θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cert.continuousOn_slice_of_smoothNbhd hsm hz
  have hf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (hslice.mul Work.FTS.EllipticEst.Cert.continuous_sinCos2_fts.continuousOn)
      |>.integrableOn_compact isCompact_Icc
  have hg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  simp only [Work.Elliptic.Fstar, Vf]
  rw [show (fun θ : ℝ => (Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
        * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ
          + Work.Elliptic.Gsing α F z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) from by
    funext θ; ring]
  rw [MeasureTheory.integral_add hf (hg.const_mul _), MeasureTheory.integral_const_mul,
    Work.Elliptic.integral_sin_two_mul_sinCos2]

/-- **The orthogonality condition identifies the singular term**: for the data of the elliptic
section with `OrthCond V`, `Gsing α F z = -(15/4)·F_*(Ψ)(z)` for every `z > -1`. -/
lemma Gsing_eq_moment (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    ∀ z : ℝ, -1 < z → Work.Elliptic.Gsing α F z = -(15 / 4) * Work.Elliptic.Fstar Ψ z := by
  intro z hz
  have h0 := hOrth z
  rw [Fstar_Vf_split α F Ψ hsm hz] at h0
  nlinarith [h0]

/-- `V` and the explicit moment form `W` agree on the open quadrant. -/
lemma Vf_eq_Wf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    Work.FTS.EllipticEst.AgreeOnQ (Vf α F Ψ) (Wf F Ψ) := by
  intro z θ hz _ _
  rw [Vf, Wf, Gsing_eq_moment α F Ψ hsm hOrth z (by linarith [hz])]
  ring

/-! ## 2. Smoothness of the explicit form -/

/-- **The angular moment `F_*(Ψ)` is analytic on `(0,∞)`** when `Ψ` is analytic on a
neighbourhood of the closed quadrant: it is the parametric `θ`-integral of the analytic
integrand `(z,θ) ↦ Ψ z θ · sinθcos²θ` over the compact interval `Iθ`
(`Coercivity.contDiffOn_setIntegral_Itheta`). -/
lemma analytic_fstar_radial (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ContDiffOn ℝ ⊤ (fun z => Work.Elliptic.Fstar Ψ z) (Set.Ioi 0) := by
  have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ))
      ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    exact ⟨lt_trans (by norm_num) (Set.mem_Ioi.mp h1), h2⟩
  have hF : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := by
    have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    exact (hsm.mono hsub).mul hsin
  have h := Work.Coercivity.contDiffOn_setIntegral_Itheta
    (fun z θ => Ψ z θ * Work.Elliptic.sinCos2 θ) hF
  simpa only [Work.Elliptic.Fstar] using h

/-- `(z,θ) ↦ F_*(Ψ)(z)·sin 2θ` is analytic on the half-strip `z > 0`, `θ ∈ (-1, π/2+1)`. -/
lemma analytic_fstar_sin_radial (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Work.Elliptic.Fstar Ψ p.1 * Real.sin (2 * p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  ((analytic_fstar_radial Ψ hsm).comp
      (contDiffOn_fst (𝕜 := ℝ)
        (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
      (fun p hp => hp.1)).mul (by fun_prop)

/-- The product `F_*(Ψ)·sin 2θ` is `C^∞` on the open quadrant. -/
lemma smoothOpen_fstar_sin (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)))
    Work.FTS.EllipticEst.Q0
  refine ((analytic_fstar_sin_radial Ψ hsm).mono ?_).of_le le_top
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ⟨hz, by linarith, by linarith [Real.pi_pos]⟩

/-- **`W` is `SmoothHalf`**: its angular slices are analytic on a neighbourhood of `[0,π/2]`
(from `SmoothNbhd Ψ`) and it is jointly analytic on the half-strip `z > 0`. -/
lemma SmoothHalf_Wf (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothHalf (Wf F Ψ) := by
  have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ))
      ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    exact ⟨lt_trans (by norm_num) (Set.mem_Ioi.mp h1), h2⟩
  constructor
  · -- angular slices
    intro z hz
    have hz1 : (-1 : ℝ) < z := by
      have hz0 : (0 : ℝ) ≤ z := hz
      linarith
    have hsliceΨ : ContDiffOn ℝ ⊤ (fun θ : ℝ => Ψ z θ) (Set.Ioo (-1) (Real.pi / 2 + 1)) := by
      have hg : ContDiffOn ℝ ⊤ (fun θ : ℝ => ((z, θ) : ℝ × ℝ))
          (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
        contDiffOn_const.prodMk contDiffOn_id
      refine (hsm.comp hg (fun θ hθ => (⟨hz1, hθ⟩ :
        ((z, θ) : ℝ × ℝ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))).congr
        (fun θ _ => rfl)
    exact hsliceΨ.add (contDiffOn_const.mul (by fun_prop))
  · -- joint analyticity on the half-strip
    have h : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ =>
        Ψ p.1 p.2 + (-(15 / 4)) * (Work.Elliptic.Fstar Ψ p.1 * Real.sin (2 * p.2)))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
      (hsm.mono hsub).add (contDiffOn_const.mul (analytic_fstar_sin_radial Ψ hsm))
    change ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ =>
      Ψ p.1 p.2 + (-(15 / 4)) * (Work.Elliptic.Fstar Ψ p.1 * Real.sin (2 * p.2)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))
    exact h

/-- `W` is smooth on the open quadrant. -/
lemma SmoothOpen_Wf (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Wf F Ψ) :=
  (SmoothHalf_Wf F Ψ hsm).smoothOpen

/-- `V` is smooth on the open quadrant. -/
lemma SmoothOpen_Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    Work.FTS.EllipticEst.SmoothOpen (Vf α F Ψ) :=
  (SmoothOpen_Wf F Ψ hsm).congr
    (fun z θ hz hθ0 hθ1 => (Vf_eq_Wf α F Ψ hsm hOrth z θ hz hθ0 hθ1).symm)

/-- `W` vanishes on the two angular boundary lines. -/
lemma VanishTheta_Wf (F Ψ : ℝ → ℝ → ℝ) (hvan : Work.Spaces.VanishTheta Ψ) :
    Work.Spaces.VanishTheta (Wf F Ψ) := by
  constructor
  · intro z
    simp only [Wf, hvan.1 z, Real.sin_zero, mul_zero, add_zero]
  · intro z
    have h : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    simp only [Wf, hvan.2 z, h, mul_zero, add_zero]

/-! ## 3. The analytic facts about `F_*`, `L₁₂` and `Gsing` -/

/-- The smoothness/`L¹` facts about the angular moment `F_*(F)` and `L₁₂(F)` derived from the
data of `EllHyp`. -/
lemma fstar_l12_facts (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) := by
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.fstar_smooth_of_sol_fts α F Ψ hHyp.smoothNbhd hHyp.sol
  have hFint : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα hHyp.smoothNbhd hHyp.sol
      hHyp.memF
  exact ⟨hFsm, hFint, Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint⟩

/-- The smoothness of `Gsing α F` on `(0,∞)` and its two relations. -/
lemma gsing_facts (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z) := by
  obtain ⟨hFsm, hFint, hL12⟩ := fstar_l12_facts α k F Ψ hα hHyp
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α F hFsm hFint hα hα1
  obtain ⟨hgsm, hode⟩ :=
    Work.FTS.EllipticEst.Cert.Gsing_smooth_ode_of_facts α F hα hFsm hFint hL12
  exact ⟨hgsm, Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ, hode⟩

/-! ## 4. The `ℋ^k`-memberships -/

/-- `F_*(Ψ)·sin 2θ ∈ ℋ^k`. -/
lemma HkMem_fstar_sin (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hmem : Work.Spaces.HkMem α k Ψ) :
    Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
  Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1
    (Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm) hmem

/-- `W ∈ ℋ^k`. -/
lemma HkMem_Wf (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k (Wf F Ψ) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm
  have hfs : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    HkMem_fstar_sin α k Ψ hα hα1 hsm hHyp.memPsi
  have hg_mem : Work.Spaces.HkMem α k
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4)) hfs
  have hg_so : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' (-(15 / 4)) (smoothOpen_fstar_sin Ψ hsm)
  have h := Work.FTS.EllipticEst.HkMem_add_open hΨso hg_so hHyp.memPsi hg_mem
  change Work.Spaces.HkMem α k
    (fun z θ : ℝ => Ψ z θ + (-(15 / 4)) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)))
  exact h

/-- `V ∈ ℋ^k` (transfer from the explicit moment form along the open quadrant). -/
lemma HkMem_Vf (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    Work.Spaces.HkMem α k (Vf α F Ψ) :=
  Work.FTS.EllipticEst.HkMem_agreeOnQ
    (g := Vf α F Ψ) (SmoothOpen_Vf α F Ψ hHyp.smoothNbhd hOrth)
    (fun z θ hz hθ0 hθ1 => (Vf_eq_Wf α F Ψ hHyp.smoothNbhd hOrth z θ hz hθ0 hθ1).symm)
    (HkMem_Wf α k F Ψ hα hα1 hHyp)

/-- The explicit form `∂_θθΨ + 15·F_*(Ψ)·sin 2θ` of `∂_θθV` lies in `ℋ^k`. -/
lemma HkMem_pth2_explicit (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k
      (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
        + 15 * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm
  have hfs : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    HkMem_fstar_sin α k Ψ hα hα1 hsm hHyp.memPsi
  exact Work.FTS.EllipticEst.HkMem_add_open
    ((Work.FTS.EllipticEst.SmoothOpen.pth hΨso).pth)
    (Work.FTS.EllipticEst.SmoothOpen.const_mul' 15 (smoothOpen_fstar_sin Ψ hsm))
    hHyp.memDth2 (Work.FTS.LocData.HkMem_const_mul α k 15 hfs)

/-- **`∂_θθ V ∈ ℋ^k`.**  On the open quadrant `∂_θθV = ∂_θθΨ + 15·F_*(Ψ)·sin 2θ`. -/
lemma HkMem_pthIter2_Vf (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Vf α F Ψ)) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm
  have hgsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0) :=
    (gsing_facts α k F Ψ hα hα1 hHyp).1
  have hGso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul hgsm (by fun_prop)
  refine Work.FTS.EllipticEst.HkMem_agreeOnQ
    (g := Work.Spaces.pthIter 2 (Vf α F Ψ))
    (Work.FTS.EllipticEst.TT.SmoothOpen_pthIter
      (Work.FTS.EllipticEst.smoothOpen_add hΨso hGso) 2)
    ?_ (HkMem_pth2_explicit α k F Ψ hα hα1 hHyp)
  intro z θ hz hθ0 hθ1
  have hadd := Work.FTS.EllipticEst.TT.pthIter_add_of_smoothOpen hΨso hGso 2 z θ hz hθ0 hθ1
  have hrad := congrFun (congrFun
    (Work.FTS.EllipticEst.TT.pthIter_two_radialSin (Work.Elliptic.Gsing α F)) z) θ
  have hgm := Gsing_eq_moment α F Ψ hsm hOrth z (by linarith)
  have hunfold : Work.Spaces.pthIter 2 (Vf α F Ψ)
      = Work.Spaces.pthIter 2
          (fun z θ : ℝ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) := rfl
  rw [hunfold, hadd, hrad, hgm]
  ring

/-- `∂_θθ W ∈ ℋ^k`: `∂_θθW = ∂_θθV` on the open quadrant. -/
lemma HkMem_pthIter2_Wf (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Wf F Ψ)) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm
  have hAQ : Work.FTS.EllipticEst.AgreeOnQ (Vf α F Ψ) (Wf F Ψ) :=
    Vf_eq_Wf α F Ψ hsm hOrth
  have hAQ2 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pthIter 2 (Vf α F Ψ))
      (Work.Spaces.pthIter 2 (Wf F Ψ)) := by
    have h1 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pth (Vf α F Ψ))
        (Work.Spaces.pth (Wf F Ψ)) := Work.FTS.EllipticEst.AgreeOnQ.pth hAQ
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using
      (Work.FTS.EllipticEst.AgreeOnQ.pth h1)
  have hso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 (Wf F Ψ)) :=
    Work.FTS.EllipticEst.TT.SmoothOpen_pthIter
      (Work.FTS.EllipticEst.smoothOpen_add hΨso
        (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-(15 / 4))
          (smoothOpen_fstar_sin Ψ hsm))) 2
  exact Work.FTS.EllipticEst.HkMem_agreeOnQ hso hAQ2
    (HkMem_pthIter2_Vf α k F Ψ hα hα1 hHyp hOrth)

/-- The explicit (scaled) form `α²z²∂_zzV = α²z²∂_zzΨ + (15/4)F_*(F)·sin 2θ
+ (25+5α)Ḡ α F·sin 2θ` lies in `ℋ^k`. -/
lemma HkMem_zsq_explicit (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α k
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + ((15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
          + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm
  obtain ⟨hFsm, hFint, -⟩ := fstar_l12_facts α k F Ψ hα hHyp
  obtain ⟨C, hC, hFlat⟩ := Work.FTS.EllipticEst.Cert.FstarSin_layer k
  have hmemFs : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    (hFlat α F Ψ hα hα4 hHyp).1
  have hmemGb : Work.Spaces.HkMem α k
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Gbar_sin α k F Ψ hα hα4 hHyp
  have hFsso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (fun n => (hFsm n).mono (Set.Ioi_subset_Ioi (by norm_num))) (by fun_prop)
  have hGbso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α F hα hFsm hFint) (by fun_prop)
  have hso₁ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    (hΨso.pzIter 2).zsq_mul.const_mul' (α ^ 2)
  have hso₂ : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.smoothOpen_add
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (15 / 4) hFsso)
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (25 + 5 * α) hGbso)
  have hm₁ : Work.Spaces.HkMem α k
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α k (α ^ 2) hHyp.memZ2
  have hm₂ : Work.Spaces.HkMem α k
      (fun z θ => (15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_add_open
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (15 / 4) hFsso)
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (25 + 5 * α) hGbso)
      (Work.FTS.LocData.HkMem_const_mul α k (15 / 4) hmemFs)
      (Work.FTS.LocData.HkMem_const_mul α k (25 + 5 * α) hmemGb)
  exact Work.FTS.EllipticEst.HkMem_add_open hso₁ hso₂ hm₁ hm₂

/-- **`z²∂_zz V ∈ ℋ^k`.** -/
lemma HkMem_zsq_pzIter2_Vf (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (Vf α F Ψ)) :
    Work.Spaces.HkMem α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hsm
  obtain ⟨hgsm, hrel, hode⟩ := gsing_facts α k F Ψ hα hα1 hHyp
  have hGso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul hgsm (by fun_prop)
  have hSso : Work.FTS.EllipticEst.SmoothOpen (Vf α F Ψ) :=
    Work.FTS.EllipticEst.smoothOpen_add hΨso hGso
  have hGderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => deriv (Work.Elliptic.Gsing α F) z') z := by
    intro z hz
    have hd : ContDiffOn ℝ (1 : WithTop ℕ∞)
        (deriv (Work.Elliptic.Gsing α F)) (Set.Ioi 0) :=
      (hgsm 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact (hd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- the pointwise identity, scaled by `α²`
  have hkey : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + ((15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
          + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ))))
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ)) := by
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have h1 := Work.FTS.EllipticEst.alphaDzIter2_straight_eq α F Ψ hα hz hθ hΨso hGso
      (hGderiv z hz) (hode z hz) (hrel z hz)
    have h2 := Work.FTS.EllipticEst.alphaDz_straight_eq α F Ψ hz hθ hΨso hGso (hrel z hz)
    have h3 := Work.FTS.EllipticEst.DzIter2_eq_zsq_pzIter2_add_Dz
      (fun z θ : ℝ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) hSso hz hθ
    have h4 := Work.FTS.EllipticEst.DzIter2_eq_zsq_pzIter2_add_Dz Ψ hΨso hz hθ
    change α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + ((15 / 4) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
          + (25 + 5 * α) * (Work.Elliptic.Gbar α F z * Real.sin (2 * θ)))
      = α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
          (fun z θ : ℝ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ)
    linear_combination -(h1) + (α ^ 2) * (h3) - (α ^ 2) * (h4) + (α / 5) * (h2)
  have hmemScaled : Work.Spaces.HkMem α k
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ)) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ
      (g := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ))
      ((hSso.pzIter 2).zsq_mul.const_mul' (α ^ 2)) hkey
      (HkMem_zsq_explicit α k F Ψ hα hα4 hHyp)
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hα)
  refine Work.FTS.EllipticEst.HkMem_agreeOnQ
    (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ)
    ((hSso.pzIter 2).zsq_mul) ?_
    (Work.FTS.LocData.HkMem_const_mul α k (1 / α ^ 2) hmemScaled)
  intro z θ _ _ _
  show (1 / α ^ 2) * (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ))
    = z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ
  rw [one_div, inv_mul_cancel_left₀ hα2]

/-! ## 5. The estimate -/

theorem coercive_input (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.EllHyp α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.Spaces.HkMem α k (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))
        ≤ C * (Work.Spaces.HkNorm α k F
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2
                (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)))
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hPoin : Work.FTS.EllipticEst.PoinHalf k hk := Work.Blocks.poincare_Half k hk
  obtain ⟨C0, hC0pos, hC0⟩ := hPoin
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro α F Ψ hα hα4 hHyp hOrth
  have hα1 : α ≤ 1 := by linarith
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hvan : Work.Spaces.VanishTheta Ψ := ⟨hHyp.sol.2.1, hHyp.sol.2.2.1⟩
  -- the memberships
  have hmemV : Work.Spaces.HkMem α k (Vf α F Ψ) := HkMem_Vf α k F Ψ hα hα1 hHyp hOrth
  have hmemZ : Work.Spaces.HkMem α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Vf α F Ψ) z θ) :=
    HkMem_zsq_pzIter2_Vf α k F Ψ hα hα4 hHyp hOrth
  -- the coercivity, applied to the explicit moment form `W`
  have hmemPthW : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Wf F Ψ)) :=
    HkMem_pthIter2_Wf α k F Ψ hα hα1 hHyp hOrth
  have hcoer := (hC0 α (Wf F Ψ) hα hα1 (SmoothHalf_Wf F Ψ hsm) (VanishTheta_Wf F Ψ hvan)
    hmemPthW).1
  -- transfers of the norms along the open quadrant
  have hAQ : Work.FTS.EllipticEst.AgreeOnQ (Vf α F Ψ) (Wf F Ψ) :=
    Vf_eq_Wf α F Ψ hsm hOrth
  have hAQ2 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pthIter 2 (Vf α F Ψ))
      (Work.Spaces.pthIter 2 (Wf F Ψ)) := by
    have h1 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pth (Vf α F Ψ))
        (Work.Spaces.pth (Wf F Ψ)) := Work.FTS.EllipticEst.AgreeOnQ.pth hAQ
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using
      (Work.FTS.EllipticEst.AgreeOnQ.pth h1)
  have hnormV : Work.Spaces.HkNorm α k (Vf α F Ψ)
      = Work.Spaces.HkNorm α k (Wf F Ψ) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
      Work.FTS.EllipticEst.HkSq_congr_open α k hAQ]
  have hnormPth : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ))
      = Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Wf F Ψ)) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
      Work.FTS.EllipticEst.HkSq_congr_open α k hAQ2]
  -- the right-hand side dominates `|∂_θθV|`
  have hle : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ))
      ≤ Work.Spaces.HkNorm α k F
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ))
        + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    have h1 : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
    have h3 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
    linarith
  have hRHSnn : 0 ≤ Work.Spaces.HkNorm α k F
      + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ))
      + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    have h1 : 0 ≤ Work.Spaces.HkNorm α k F := Work.Spaces.HkNorm_nonneg α k F
    have h2 : 0 ≤ Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ)) :=
      Work.Spaces.HkNorm_nonneg α k _
    have h3 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
    linarith
  refine ⟨hmemV, hmemZ, ?_⟩
  calc Work.Spaces.HkNorm α k (Vf α F Ψ) = Work.Spaces.HkNorm α k (Wf F Ψ) := hnormV
    _ ≤ C0 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Wf F Ψ)) := hcoer
    _ = C0 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ)) := by rw [hnormPth]
    _ ≤ (C0 + 1) * (Work.Spaces.HkNorm α k F
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Vf α F Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
        refine le_trans (mul_le_mul_of_nonneg_left hle (le_of_lt hC0pos)) ?_
        exact mul_le_mul_of_nonneg_right (by linarith) hRHSnn

end Work.FTS.EllipticEst.Straight
