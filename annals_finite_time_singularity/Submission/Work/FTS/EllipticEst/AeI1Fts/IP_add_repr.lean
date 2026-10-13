import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.H2W.WeakAux.I1ZibpOpenAbs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/IP_add_repr` — the additive representation of the `ω²σ`-pairing

The `I₁` chain of Elgindi, Annals 194 (3) 2021, splits the pairing
`IP (AA u) (BB u) + IP (cw·U u) (BB u)` into the single iterated integral

`∫_z w(z)² ∫_θ sin(2θ)^{-η} (AA·BB + cw·U·BB)`.

The pairing `AngSecond.IP g h = ∫_z ∫_θ g h w² σ` is a *totalised* (Bochner) double integral, so
the split is **not** free: adding the two iterated integrals and merging them into one requires the
joint integrability of the two integrands.  That is supplied here by
`H2W.WeakAux.prod_integrable_mul` (Fubini + the arithmetic–geometric mean inequality against the
`ℋ⁰`-integrands of `AA u`, `U u`, `BB u`), which applies verbatim because `u` is `C^∞` on the open
quadrant (`AeData.smooth`, hence `SmoothOpen u`) so that `AA u`, `BB u`, `U u` and `cw · U u` are
continuous on `(0,∞) × (0,π/2)`, and because the three hypotheses `HkMem α 0` are honest.

The `z`-pairing `cw z = 2(z-1)/(1+z)` is bounded by `2` on `[0,∞)`, so `cw · U u` is again
`ℋ⁰`-honest (`HkMem_cw_mul`).

* `IP_repr` — the representation of the pairing as a single iterated integral over
  `(0,∞) × (0,π/2)` with `w²` pulled out; it is *hypothesis-free* (interval bookkeeping on null
  sets plus `integral_const_mul`);
* `HkMem_cw_mul` — `HkMem α 0 (cw · f)` from `HkMem α 0 f`;
* `IP_add_repr` — the target.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Interval bookkeeping for `IP`

(The two lemmas below are *private*: `AeI1Fts/identity.lean` declares the same two statements
publicly under the same names, and both modules are in the cone of `AeI1Fts/identity_local.lean`
once `radial_identity` imports the assembled `radial_alt`; a duplicate public declaration there
is an error.  Nothing in this development uses the public names from this file.) -/

/-- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`. -/
private theorem integral_Iz_eq_Ioi (f : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z :=
  MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- `Iθ = [0,π/2]` and `(0,π/2)` differ by the null set `{0,π/2}`. -/
private theorem integral_Iθ_eq_Ioo (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Iθo, f θ :=
  MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm

/-- **Representation of the weighted pairing as one iterated integral with `w²` pulled out.**

For arbitrary (not necessarily integrable) profiles,
`IP g h = ∫_{z>0} w(z)² ∫_{0<θ<π/2} sin(2θ)^{-η} · g z θ · h z θ`. -/
theorem IP_repr (g h : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.AngSecond.IP g h
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2
          * ∫ θ in Iθo, sigE θ * (g z θ * h z θ) := by
  have hIz : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
    integral_Iz_eq_Ioi _
  rw [Work.FTS.EllipticEst.AngSecond.IP, hIz]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  have hIθ : (∫ θ in Work.Spaces.Iθ,
        g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ θ in Iθo, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    integral_Iθ_eq_Ioo _
  rw [hIθ]
  have hre : (fun θ => g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      = fun θ => (Work.Spaces.w z) ^ 2 * (g z θ * h z θ * sigE θ) := by
    funext θ
    show g z θ * h z θ * (Work.Spaces.w z) ^ 2 * sigE θ
        = (Work.Spaces.w z) ^ 2 * (g z θ * h z θ * sigE θ)
    ring
  rw [hre, MeasureTheory.integral_const_mul]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  ring

/-! ## `ℋ⁰`-honesty of `cw · f` -/

/-- **`cw` is bounded by `2` on `Iz`.** -/
theorem abs_cw_le_two_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |Work.FTS.EllipticEst.AngSecond.cw z| ≤ 2 :=
  Work.FTS.EllipticEst.AngSecond.abs_cw_le_two (Set.mem_Ici.mp hz)

/-- **`ℋ⁰`-honesty of `cw · f`.**  Since `|cw z| ≤ 2` on `Iz`, the `ℋ⁰`-integrand of `cw · f`
is `cw z²` times that of `f` on every angular slice, and the `z`-integrand is a bounded multiple
of the `z`-integrand of `f`. -/
theorem HkMem_cw_mul {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    Work.Spaces.HkMem α 0 (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * f z θ) := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * f z θ) z θ
      = Work.FTS.EllipticEst.AngSecond.cw z ^ 2
        * Work.Spaces.HkIntegrand α 0 f z θ := by
    intro z θ
    rw [Work.FTS.EllipticEst.H2W.WeakAux.HkIntegrand_zero_eq,
      Work.FTS.EllipticEst.H2W.WeakAux.HkIntegrand_zero_eq]
    ring
  constructor
  · intro z hz
    refine ((hf.1 z hz).const_mul (Work.FTS.EllipticEst.AngSecond.cw z ^ 2)).congr
      (Eventually.of_forall (fun θ => ?_))
    exact (hpt z θ).symm
  · have hcm : Measurable (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z ^ 2) := by
      have hfun : (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z ^ 2)
          = fun z : ℝ => (2 * (z - 1) / (1 + z)) ^ 2 := by
        funext z; rw [Work.FTS.EllipticEst.AngSecond.cw]
      rw [hfun]
      fun_prop
    have hbd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
        ‖Work.FTS.EllipticEst.AngSecond.cw z ^ 2‖ ≤ (4 : ℝ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := abs_cw_le_two_Iz hz
      nlinarith [abs_nonneg (Work.FTS.EllipticEst.AngSecond.cw z),
        sq_abs (Work.FTS.EllipticEst.AngSecond.cw z)]
    have hout : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.AngSecond.cw z ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)) Work.Spaces.Iz :=
      hf.2.bdd_mul hcm.aestronglyMeasurable hbd
    refine hout.congr (Eventually.of_forall (fun z => ?_))
    show Work.FTS.EllipticEst.AngSecond.cw z ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * f z θ) z θ
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => (hpt z θ).symm)

/-! ## The additive representation -/

local notation "Qd0" => Work.FTS.EllipticEst.H2W.WeakAux.Qd0
local notation "muP" => Work.FTS.EllipticEst.H2W.WeakAux.muP

theorem IP_add_repr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hA : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.AA u))
    (hB : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.BB u)) :
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeI1Fts.AA u)
        (Work.FTS.EllipticEst.AeI1Fts.BB u)
      + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AeI1Fts.U u z θ)
          (Work.FTS.EllipticEst.AeI1Fts.BB u)
      = ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * (Work.FTS.EllipticEst.AeI1Fts.AA u z θ * Work.FTS.EllipticEst.AeI1Fts.BB u z θ
                + Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAAc : ContinuousOn (Function.uncurry (AA u)) Qd0 := (smoothOpen_AA hS).continuousOn
  have hBBc : ContinuousOn (Function.uncurry (BB u)) Qd0 := (smoothOpen_BB hS).continuousOn
  have hUc : ContinuousOn (Function.uncurry (U u)) Qd0 := (smoothOpen_U hS).continuousOn
  have hcwOn : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z)
      (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z)
        = fun z : ℝ => 2 * (z - 1) / (1 + z) := by
      funext z; rw [Work.FTS.EllipticEst.AngSecond.cw]
    rw [hfun]
    refine ContinuousOn.div (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
      (continuousOn_const.add continuousOn_id)
      (fun z hz => ne_of_gt (by linarith [show (0 : ℝ) < z from hz]))
  have hcwUc : ContinuousOn
      (Function.uncurry (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ)) Qd0 :=
    (hcwOn.comp continuousOn_fst (fun p hp => hp.1)).mul hUc
  have hcwUmem : Work.Spaces.HkMem α 0
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) := HkMem_cw_mul hU
  have hF1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => AA u p.1 p.2 * BB u p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2) muP :=
    Work.FTS.EllipticEst.H2W.WeakAux.prod_integrable_mul hAAc hBBc hA hB
  have hF2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.FTS.EllipticEst.AngSecond.cw p.1 * U u p.1 p.2) * BB u p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2) muP :=
    Work.FTS.EllipticEst.H2W.WeakAux.prod_integrable_mul hcwUc hBBc hcwUmem hB
  have hF12 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (AA u p.1 p.2 + Work.FTS.EllipticEst.AngSecond.cw p.1 * U u p.1 p.2) * BB u p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2) muP :=
    (hF1.add hF2).congr (Eventually.of_forall (fun p => by simp only [Pi.add_apply]; ring))
  have e1 : Work.FTS.EllipticEst.AngSecond.IP (AA u) (BB u)
      = ∫ p, AA u p.1 p.2 * BB u p.1 p.2
          * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * Work.FTS.EllipticEst.AngSecond.sig p.2 ∂muP :=
    (MeasureTheory.integral_prod _ hF1).symm
  have e2 : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u)
      = ∫ p, (Work.FTS.EllipticEst.AngSecond.cw p.1 * U u p.1 p.2) * BB u p.1 p.2
          * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * Work.FTS.EllipticEst.AngSecond.sig p.2 ∂muP :=
    (MeasureTheory.integral_prod _ hF2).symm
  have e3 : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => AA u z θ + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u)
      = ∫ p, (AA u p.1 p.2 + Work.FTS.EllipticEst.AngSecond.cw p.1 * U u p.1 p.2)
          * BB u p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * Work.FTS.EllipticEst.AngSecond.sig p.2 ∂muP :=
    (MeasureTheory.integral_prod _ hF12).symm
  have hmain : Work.FTS.EllipticEst.AngSecond.IP (AA u) (BB u)
      + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u)
      = Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => AA u z θ + Work.FTS.EllipticEst.AngSecond.cw z * U u z θ) (BB u) := by
    rw [e1, e2, e3, ← MeasureTheory.integral_add hF1 hF2]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun p => by ring))
  rw [hmain, IP_repr]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  ring

end Work.FTS.EllipticEst.AeI1Fts
