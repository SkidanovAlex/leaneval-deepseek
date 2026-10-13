/-
# `Work.FTS.EllSol.ellClassO_lin` — the solution class `EllClassO` is closed under linear
combinations

This file proves item **(c)** of `Submission/Work/FTS/FTS_ELL_GALERKIN.md` §1:

> `ellClassO_lin` — `EllClassO` is closed under linear combinations.

## The content

`EllClassO α g Ψ = IsBslSol α g Ψ ∧ SmoothOpen Ψ ∧ EllWeakPos α 4 (orthSource g) (Ψ + G·sin 2θ)`
(`G = Gsing α g`).  Each of the three conjuncts is linear in `(g, Ψ)`, but the *third* one is
linear only modulo the explicit identity

  `Gsing α (g + c·g') = Gsing α g + c·Gsing α g'`   (on `(0,∞)`),

which is not a definitional identity: `Gsing α F = -(1/(4α))·L₁₂(F) + Ḡ(α,F)` is built from the
angular moment `F_*` and the two integral operators `L₁₂` and `Ḡ`, all of which are linear only
on functions whose slices are integrable.  The file therefore proceeds in three layers:

* **linearity of the ingredients** (`Fstar`, `L12dens`, `L12`, `Gbar`, `Gsing`, `orthSource`) —
  `Fstar_add_mul` … `Gsing_add_mul`;
* **closure of the weak class** `EllWeakPos` under linear combinations
  (`EllWeakPos_add_mul`) and under agreement on the open quadrant (`EllWeakPos_congr_Q0`); the
  second moment of the shifted unknown is handled by `Fstar_add_mul` applied to the *shifted*
  functions, whose angular slices are integrable for every `z > 0` by
  `EllWeakPos.slice_sinCos2_integrable` (from `HkMem α 0 (∂_θθ·)` and the Dirichlet data);
* **assembly** (`ellClassO_lin`).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Cores.OrthCond_lambda_zero
import Submission.Work.FTS.EllipticEst.Dispatch.aeLeftLimitD
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.Straight_DzHk_le
import Submission.Work.Elliptic.Fstar_orthSource
import Submission.Work.FTS.EllExist.Shift
import Submission.Work.FM.Core
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.Elliptic.GsingFuncs
import Submission.Work.FTS.EllSol.L12densIntegrableNoAlpha
import Submission.Work.FTS.EllSol.intervalIntegrable_rpow_Fstar

import Submission.Work.FTS.EllSol.EllAux1
import Submission.Work.FTS.H2.PhiStarE5.Locality

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2
local notation "Kθ" => Work.Elliptic.Ktheta
/-! ## Linearity of `L₁₂` -/

/-- Additivity (with a scalar) of `L₁₂` at `z > 0`, from additivity of the densities on
`(0,∞)` and the integrability of the two densities on `(z,∞)`. -/
theorem L12_add_mul {f h : ℝ → ℝ → ℝ} {c z : ℝ} (hz : 0 ≤ z)
    (hd : ∀ s, 0 < s → Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s)
    (hF : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens f) (Set.Ioi z))
    (hH : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens h) (Set.Ioi z)) :
    Work.Elliptic.L12 (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.L12 f z + c * Work.Elliptic.L12 h z := by
  rw [Work.Elliptic.L12, Work.Elliptic.L12, Work.Elliptic.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => hd s (lt_of_le_of_lt hz hs))]
  rw [MeasureTheory.integral_add hF (hH.const_mul c), MeasureTheory.integral_const_mul]

/-! ## Linearity of `Ḡ` -/

/-- Additivity (with a scalar) of `Ḡ(α,·)` at `z > 0`, from additivity of `F_*` on `(0,∞)` and
the interval integrability of the two integrands on `(0,z)`. -/
theorem Gbar_add_mul {α : ℝ} {f h : ℝ → ℝ → ℝ} {c z : ℝ} (hz : 0 < z)
    (hd : ∀ s, 0 < s → Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.Fstar f s + c * Work.Elliptic.Fstar h s)
    (hf : IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar f s)
      MeasureTheory.volume 0 z)
    (hh : IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar h s)
      MeasureTheory.volume 0 z) :
    Work.Elliptic.Gbar α (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Gbar α f z + c * Work.Elliptic.Gbar α h z := by
  rw [Work.Elliptic.Gbar, Work.Elliptic.Gbar, Work.Elliptic.Gbar]
  have hcongr : (∫ s in (0 : ℝ)..z,
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s)
      = ∫ s in (0 : ℝ)..z,
          (s ^ ((5 - α) / α) * Work.Elliptic.Fstar f s
            + c * (s ^ ((5 - α) / α) * Work.Elliptic.Fstar h s)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [hd s (Set.mem_Ioc.mp hs).1]
    ring
  rw [hcongr, intervalIntegral.integral_add hf (hh.const_mul c),
    intervalIntegral.integral_const_mul]
  ring

/-- Homogeneity of `Ḡ(α,·)` (no integrability hypothesis). -/
theorem Gbar_const_mul (α c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Gbar α (fun z θ => c * f z θ) z
      = c * Work.Elliptic.Gbar α f z := by
  rw [Work.Elliptic.Gbar, Work.Elliptic.Gbar,
    show (∫ s in (0 : ℝ)..z,
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar (fun z θ => c * f z θ) s)
        = ∫ s in (0 : ℝ)..z, c * (s ^ ((5 - α) / α) * Work.Elliptic.Fstar f s) from by
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [Fstar_const_mul]
      ring]
  rw [intervalIntegral.integral_const_mul]
  ring

/-! ## Linearity of the singular term `Gsing` -/

/-- **`Gsing` is additive** (with a scalar) at every `z > 0`: the singular term of
§'The singular term' is linear in the source, its three ingredients (`F_*`, `L₁₂`, `Ḡ`) being
linear on the `ℋ⁴`-data with smooth open-quadrant slices. -/
theorem Gsing_add_mul {α : ℝ} (hα : 0 < α) {f h : ℝ → ℝ → ℝ} (c : ℝ) {z : ℝ} (hz : 0 < z)
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hmemf : Work.Spaces.HkMem α 4 f)
    (hsmh : Work.FTS.LocData.SmoothQuad h) (hmemh : Work.Spaces.HkMem α 4 h) :
    Work.Elliptic.Gsing α (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Gsing α f z + c * Work.Elliptic.Gsing α h z := by
  have hsof : Work.FTS.EllipticEst.SmoothOpen f := smoothOpen_of_smoothQuad hsmf
  have hsoh : Work.FTS.EllipticEst.SmoothOpen h := smoothOpen_of_smoothQuad hsmh
  have hmemf0 : Work.Spaces.HkMem α 0 f :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 4) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsof) hmemf
  have hmemh0 : Work.Spaces.HkMem α 0 h :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 4) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h).mp hsoh) hmemh
  -- additivity of `F_*`
  have hFs : ∀ s, 0 < s → Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.Fstar f s + c * Work.Elliptic.Fstar h s := fun s hs =>
    Fstar_add_mul
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsof.continuousOn hmemf0 hs)
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoh.continuousOn hmemh0 hs)
  -- additivity of the `L₁₂`-densities
  have hdens : ∀ s, 0 < s →
      Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
        = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s := fun s hs =>
    L12dens_add_mul (L12dens_slice_integrable hsof.continuousOn hmemf hs)
      (L12dens_slice_integrable hsoh.continuousOn hmemh hs)
  -- integrability of the densities on `(z,∞)`
  have hDf : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens f) (Set.Ioi z) :=
    (L12densIntegrableNoAlpha α f hsmf hmemf).mono_set (Set.Ioi_subset_Ioi hz.le)
  have hDh : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens h) (Set.Ioi z) :=
    (L12densIntegrableNoAlpha α h hsmh hmemh).mono_set (Set.Ioi_subset_Ioi hz.le)
  -- interval integrability of the `Ḡ`-integrands
  have hIf : IntervalIntegrable
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar f s) MeasureTheory.volume 0 z :=
    intervalIntegrable_rpow_Fstar α hα f hsmf hmemf hz
  have hIh : IntervalIntegrable
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar h s) MeasureTheory.volume 0 z :=
    intervalIntegrable_rpow_Fstar α hα h hsmh hmemh hz
  rw [Work.Elliptic.Gsing, Work.Elliptic.Gsing, Work.Elliptic.Gsing]
  rw [show Work.Elliptic.Gstar α (fun z θ => f z θ + c * h z θ) z
      = -(1 / (4 * α)) * Work.Elliptic.L12 (fun z θ => f z θ + c * h z θ) z from rfl]
  rw [L12_add_mul hz.le hdens hDf hDh, Gbar_add_mul hz hFs hIf hIh]
  rw [show Work.Elliptic.Gstar α f z = -(1 / (4 * α)) * Work.Elliptic.L12 f z from rfl,
    show Work.Elliptic.Gstar α h z = -(1 / (4 * α)) * Work.Elliptic.L12 h z from rfl]
  ring

/-! ## Moment of the shifted unknown of a datum of the weak class -/

/-- The angular slice of the unknown of an `EllWeakPos` datum is integrable against
`sinθcos²θ` for every `z > 0`: `HkMem α 0 (∂_θθ·)` together with the two Dirichlet values
bounds the slice (`Endpt.sliceBdd_of_hmB`). -/
theorem EllWeakPos.slice_sinCos2_integrable {α : ℝ} {k : ℕ} {F S : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F S) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => S z θ * sg θ) Iθ := by
  have hso : Work.FTS.EllipticEst.SmoothOpen S :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmem0 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 S) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := k) (by omega)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hso.pth.pth)) h.memB
  exact Work.FTS.EllipticEst.Dispatch.slice_mul_sinCos2_integrableD h.smooth hmem0 hz
    (h.zero z) (h.pi_half z)

/-! ## Closure of the weak class under linear combinations -/

/-- **`EllWeakPos` is closed under linear combinations** (for sources which are `C^∞` on the
open quadrant and whose combination satisfies the solvability condition). -/
theorem EllWeakPos_add_mul {α : ℝ} {k : ℕ} {F F' S S' : ℝ → ℝ → ℝ} {c : ℝ}
    (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hsmF' : Work.FTS.EllipticEst.SmoothOpen F')
    (horth : ∀ z, 0 < z → Work.Elliptic.Fstar (fun z θ => F z θ + c * F' z θ) z = 0)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F S)
    (h' : Work.FTS.EllipticEst.TT.EllWeakPos α k F' S') :
    Work.FTS.EllipticEst.TT.EllWeakPos α k (fun z θ => F z θ + c * F' z θ)
      (fun z θ => S z θ + c * S' z θ) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen S :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hso' : Work.FTS.EllipticEst.SmoothOpen S' :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h'.smooth
  have hcso' : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * S' z θ) := hso'.const_mul' c
  have hcS' : (fun z θ => c * S' z θ) = c • S' := by
    funext z θ; simp only [Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, horth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation
    intro z hz θ h0 h1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
    have hb1 : Work.Elliptic.bslOp α (fun z θ => S z θ + c * S' z θ) z θ
        = Work.Elliptic.bslOp α S z θ
          + Work.Elliptic.bslOp α (fun z θ => c * S' z θ) z θ :=
      Work.Elliptic.bslOp_add α S (fun z θ => c * S' z θ) z θ hcos
        (smoothOpen_contDiffAt_two hso hz h0 h1) (smoothOpen_contDiffAt_two hcso' hz h0 h1)
    have hb2 : Work.Elliptic.bslOp α (fun z θ => c * S' z θ) z θ
        = c * Work.Elliptic.bslOp α S' z θ := by
      have hs := Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul α c S' z θ
      rw [← hcS'] at hs
      exact hs
    rw [hb1, hb2, h.eq z hz θ h0 h1, h'.eq z hz θ h0 h1]
  · intro z; simp only [Pi.add_apply]; rw [h.zero z, h'.zero z]; ring
  · intro z; simp only [Pi.add_apply]; rw [h.pi_half z, h'.pi_half z]; ring
  · -- the moment of the unknown
    intro z hz
    rw [Fstar_add_mul (EllWeakPos.slice_sinCos2_integrable h hz)
      (EllWeakPos.slice_sinCos2_integrable h' hz), h.orthPsi z hz, h'.orthPsi z hz]
    ring
  · -- smoothness
    intro n
    have hfun : Function.uncurry (fun z θ => S z θ + c * S' z θ)
        = Function.uncurry S + c • Function.uncurry S' := by
      funext p
      simp only [Function.uncurry, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact (h.smooth n).add ((h'.smooth n).const_smul c)
  · -- the source, in `ℋ^k`
    exact Work.FTS.LocData.HkMem_const_mul α k c h'.memF |> fun hmem =>
      Work.FTS.EllipticEst.HkMem_add_open hsmF (hsmF'.const_mul' c) h.memF hmem
  · -- `z²∂_z²` of the unknown
    have hlin : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pzIter 2 (fun z θ => S z θ + c * S' z θ) z θ
          = Work.Spaces.pzIter 2 S z θ + c * Work.Spaces.pzIter 2 S' z θ := by
      intro z θ hz h0 h1
      rw [pzIter_add_open (f := S) (g := fun z θ => c * S' z θ) hso hcso' 2 z θ hz h0 h1,
        show Work.Spaces.pzIter 2 (fun z θ => c * S' z θ)
            = c • Work.Spaces.pzIter 2 S' from by rw [hcS', Work.FTS.EllipticEst.pzIter_smul]]
      simp only [Pi.smul_apply, smul_eq_mul]
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (u := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 S z θ
        + c * (z ^ 2 * Work.Spaces.pzIter 2 S' z θ)) ?_ ?_
    · exact Work.FTS.EllipticEst.HkMem_add_open ((hso.pzIter 2).zsq_mul)
        ((hso'.pzIter 2).zsq_mul.const_mul' c) h.memA
        (Work.FTS.LocData.HkMem_const_mul α k c h'.memA)
    · intro z hz θ hθ
      show z ^ 2 * Work.Spaces.pzIter 2 S z θ + c * (z ^ 2 * Work.Spaces.pzIter 2 S' z θ)
        = z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => S z θ + c * S' z θ) z θ
      rw [hlin z θ hz hθ.1 hθ.2]
      ring
  · -- `∂_θ²` of the unknown
    have hlin : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ) z θ
          = Work.Spaces.pthIter 2 S z θ + c * Work.Spaces.pthIter 2 S' z θ := by
      intro z θ hz h0 h1
      rw [Work.FTS.EllipticEst.pthIter_add_of_smoothOpen (f := S)
        (g := fun z θ => c * S' z θ) hso hcso' 2 z θ hz h0 h1,
        show Work.Spaces.pthIter 2 (fun z θ => c * S' z θ)
            = c • Work.Spaces.pthIter 2 S' from by rw [hcS', Work.FTS.EllipticEst.pthIter_smul]]
      simp only [Pi.smul_apply, smul_eq_mul]
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (u := fun z θ => Work.Spaces.pthIter 2 S z θ
        + c * Work.Spaces.pthIter 2 S' z θ) ?_ ?_
    · exact Work.FTS.EllipticEst.HkMem_add_open (hso.pth.pth)
        ((hso'.pth.pth).const_mul' c) h.memB
        (Work.FTS.LocData.HkMem_const_mul α k c h'.memB)
    · intro z hz θ hθ
      show Work.Spaces.pthIter 2 S z θ + c * Work.Spaces.pthIter 2 S' z θ
        = Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ) z θ
      rw [hlin z θ hz hθ.1 hθ.2]
  · -- `z∂_z∂_θ²` of the unknown
    have hlin : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ)) z θ
          = Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
            + c * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ := by
      intro z θ hz h0 h1
      have hloc : Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ)) z θ
          = Work.Spaces.pz (fun z θ => Work.Spaces.pthIter 2 S z θ
              + c * Work.Spaces.pthIter 2 S' z θ) z θ := by
        rw [Work.Spaces.pz, Work.Spaces.pz]
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        have hlin' : ∀ θ', 0 < θ' → θ' < π / 2 →
            Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ) z' θ'
              = Work.Spaces.pthIter 2 S z' θ' + c * Work.Spaces.pthIter 2 S' z' θ' := by
          intro θ' h0' h1'
          rw [Work.FTS.EllipticEst.pthIter_add_of_smoothOpen (f := S)
        (g := fun z θ => c * S' z θ) hso hcso' 2 z' θ' hz' h0' h1',
            show Work.Spaces.pthIter 2 (fun z θ => c * S' z θ)
                = c • Work.Spaces.pthIter 2 S' from by
              rw [hcS', Work.FTS.EllipticEst.pthIter_smul]]
          simp only [Pi.smul_apply, smul_eq_mul]
        exact hlin' θ h0 h1
      rw [hloc, pz_add_open (f := Work.Spaces.pthIter 2 S)
        (g := fun z θ => c * Work.Spaces.pthIter 2 S' z θ)
        (hso.pth.pth) ((hso'.pth.pth).const_mul' c) hz h0 h1]
      rw [show Work.Spaces.pz (fun z θ => c * Work.Spaces.pthIter 2 S' z θ) z θ
          = c * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ from by
        rw [show (fun z θ => c * Work.Spaces.pthIter 2 S' z θ)
            = c • (Work.Spaces.pthIter 2 S') from by
          funext z' θ'; simp only [Pi.smul_apply, smul_eq_mul],
          Work.FTS.EllipticEst.pz_smul]
        simp only [Pi.smul_apply, smul_eq_mul]]
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (u := fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
        + c * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ)) ?_ ?_
    · exact Work.FTS.EllipticEst.HkMem_add_open (smoothOpen_z_mul ((hso.pth.pth).pz))
        ((smoothOpen_z_mul ((hso'.pth.pth).pz)).const_mul' c) h.memZPth2
        (Work.FTS.LocData.HkMem_const_mul α k c h'.memZPth2)
    · intro z hz θ hθ
      show z * Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
          + c * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ)
        = z * Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => S z θ + c * S' z θ)) z θ
      rw [hlin z θ hz hθ.1 hθ.2]
      ring

/-! ## Congruence of the weak class along the open quadrant -/

/-- **`EllWeakPos` only depends on the values on the open quadrant.**  Two data agreeing there
(for the source, the equation transfers by locality of `bslOp`; for the unknown, by the
a.e.-congruence of `F_*` and of the `ℋ^k`-integrands) and having the prescribed Dirichlet
values are simultaneously in the class. -/
theorem EllWeakPos_congr_Q0 {α : ℝ} {k : ℕ} {F F' S S' : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F S)
    (hF : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = F' z θ)
    (hS : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → S z θ = S' z θ)
    (h0 : ∀ z, S' z 0 = 0) (hpi : ∀ z, S' z (π / 2) = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k F' S' := by
  have hQ : EqOn (Function.uncurry S) (Function.uncurry S') Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    show S p.1 p.2 = S' p.1 p.2
    exact hS p.1 p.2 h1 h2 h3
  refine ⟨?_, h0, hpi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation
    intro z hz θ h0' h1'
    have hev : ∀ᶠ q in 𝓝 (z, θ), S' q.1 q.2 = S q.1 q.2 :=
      Filter.eventually_of_mem
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0', h1'⟩))
        (fun q hq => (hQ hq).symm)
    rw [Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq α hev,
      h.eq z hz θ h0' h1']
    exact hF z θ hz h0' h1'
  · -- the moment of the source
    intro z hz
    rw [Fstar_congr_Ioo (f := F') (h := F) (fun θ h0' h1' => (hF z θ hz h0' h1').symm)]
    exact h.orthF z hz
  · -- the moment of the unknown
    intro z hz
    rw [Fstar_congr_Ioo (f := S') (h := S) (fun θ h0' h1' => (hS z θ hz h0' h1').symm)]
    exact h.orthPsi z hz
  · -- smoothness
    intro n
    exact (h.smooth n).congr fun p hp => (hQ hp).symm
  · -- the source, in `ℋ^k`
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memF ?_
    intro z hz θ hθ
    exact hF z θ hz hθ.1 hθ.2
  · -- `z²∂_z²` of the unknown
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memA ?_
    intro z hz θ hθ
    show z ^ 2 * Work.Spaces.pzIter 2 S z θ = z ^ 2 * Work.Spaces.pzIter 2 S' z θ
    rw [pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hQ 2 z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
  · -- `∂_θ²` of the unknown
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memB ?_
    intro z hz θ hθ
    show Work.Spaces.pthIter 2 S z θ = Work.Spaces.pthIter 2 S' z θ
    rw [pthIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hQ 2 z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]
  · -- `z∂_z∂_θ²` of the unknown
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h.memZPth2 ?_
    intro z hz θ hθ
    show z * Work.Spaces.pz (Work.Spaces.pthIter 2 S) z θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 S') z θ
    have hEq : EqOn (Function.uncurry (Work.Spaces.pthIter 2 S))
        (Function.uncurry (Work.Spaces.pthIter 2 S')) Work.FTS.EllipticEst.Q0 :=
      fun p hp => pthIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hQ 2 p.1 p.2 hp
    rw [Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)]

end Work.FTS.EllSol
