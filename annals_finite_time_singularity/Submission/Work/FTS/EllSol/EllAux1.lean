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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2
local notation "Kθ" => Work.Elliptic.Ktheta

/-! ## Elementary facts about the angle interval -/

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
  Work.Elliptic.ae_restrict_Iθ_of_Ioo fun θ h0 h1 => ⟨h0, h1⟩

/-! ## Smoothness on the open quadrant from `SmoothQuad` -/

/-- `SmoothQuad` (smoothness on the open strip `z > -1`) implies `SmoothOpen` (smoothness on the
open quadrant `z > 0`). -/
theorem smoothOpen_of_smoothQuad {g : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad g) : Work.FTS.EllipticEst.SmoothOpen g :=
  h.mono fun p hp => by
    obtain ⟨h1, h2, h3⟩ := hp
    exact ⟨Set.mem_Ioi.mpr (by linarith [show (0 : ℝ) < p.1 from h1]), Set.mem_Ioo.mpr ⟨h2, h3⟩⟩

/-- `C²` at a point of the open quadrant, from `SmoothOpen`. -/
theorem smoothOpen_contDiffAt_two {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    ContDiffAt ℝ 2 (Function.uncurry F) (z, θ) :=
  (h.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩))).of_le (by simp [Work.Stability.smoothOrder])

/-- `SmoothOpen` is closed under multiplication by `z`. -/
theorem smoothOpen_z_mul {A : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * A z θ) := by
  have hfun : Function.uncurry (fun z θ => z * A z θ)
      = fun p : ℝ × ℝ => p.1 * A p.1 p.2 := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => A p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    hA.comp contDiffOn_id fun p hp => hp
  exact h1.mul h2

/-! ## Linearity and locality of the iterated derivatives -/

/-- `∂_z` is additive on `SmoothOpen` data. -/
theorem pz_add_open {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz g z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_add (hf.hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt
    (hg.hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt

/-- `∂_z`-iterates are additive on `SmoothOpen` data. -/
theorem pzIter_add_open {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pzIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pzIter i f z θ + Work.Spaces.pzIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h0 h1
      simp only [Work.Spaces.pzIter_succ]
      rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
      have hev : (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter n f z' θ + Work.Spaces.pzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h0 h1
      rw [Filter.EventuallyEq.deriv_eq hev]
      exact deriv_add ((hf.pzIter n).hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt
        ((hg.pzIter n).hasDerivAt_slice ⟨h0, h1⟩ hz).differentiableAt

/-- `∂_z`-iterates only see the values on an open set. -/
theorem pzIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry u) (Function.uncurry v) V) (j : ℕ) :
    ∀ z θ, (z, θ) ∈ V → Work.Spaces.pzIter j u z θ = Work.Spaces.pzIter j v z θ := by
  induction j with
  | zero => intro z θ hz; exact h hz
  | succ n ih =>
      intro z θ hz
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
      exact Work.Spaces.pz_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-- `∂_θ`-iterates only see the values on an open set. -/
theorem pthIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry u) (Function.uncurry v) V) (j : ℕ) :
    ∀ z θ, (z, θ) ∈ V → Work.Spaces.pthIter j u z θ = Work.Spaces.pthIter j v z θ := by
  induction j with
  | zero => intro z θ hz; exact h hz
  | succ n ih =>
      intro z θ hz
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ]
      exact Work.Spaces.pth_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-! ## Linearity of the angular moment `F_*` -/

/-- **`F_*` is additive** (with a scalar) on slices whose product with `sinθcos²θ` is
integrable. -/
theorem Fstar_add_mul {f h : ℝ → ℝ → ℝ} {c z : ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => f z θ * sg θ) Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => h z θ * sg θ) Iθ) :
    Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Fstar f z + c * Work.Elliptic.Fstar h z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (∫ θ in Iθ, (f z θ + c * h z θ) * sg θ)
      = ∫ θ in Iθ, (f z θ * sg θ + c * (h z θ * sg θ)) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_add hf (hh.const_mul c), MeasureTheory.integral_const_mul]

/-- **`F_*` is homogeneous** (no integrability hypothesis: the Bochner integral is total). -/
theorem Fstar_const_mul (f : ℝ → ℝ → ℝ) (c z : ℝ) :
    Work.Elliptic.Fstar (fun z θ => c * f z θ) z = c * Work.Elliptic.Fstar f z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar,
    show (∫ θ in Iθ, (c * f z θ) * sg θ) = ∫ θ in Iθ, c * (f z θ * sg θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## The elements of the Galerkin class

`GalClass α g` is a structure whose `reg` field is `RegQ α 6 g = SmoothQuad g ∧ HkMem α 6 g ∧
BdryTraces α 6 g`. -/

theorem GalClass.smoothQuad {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.LocData.SmoothQuad g := hg.reg.1

theorem GalClass.hkMem_six {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.HkMem α 6 g := hg.reg.2.1

theorem GalClass.smoothOpen {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.EllipticEst.SmoothOpen g := smoothOpen_of_smoothQuad (GalClass.smoothQuad hg)

theorem GalClass.contDiffOn_uncurry {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp (GalClass.smoothOpen hg)

theorem GalClass.hkMem_le {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) {k : ℕ}
    (hk : k ≤ 6) : Work.Spaces.HkMem α k g :=
  Work.FTS.EllipticEst.TT.HkMem_descend_open hk (GalClass.contDiffOn_uncurry hg)
    (GalClass.hkMem_six hg)

theorem GalClass.hkMem_zero {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.HkMem α 0 g := GalClass.hkMem_le hg (by norm_num)

theorem GalClass.hkMem_four {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.HkMem α 4 g := GalClass.hkMem_le hg (by norm_num)

theorem GalClass.vanishTheta {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.VanishTheta g := hg.vanish

/-- The angular slice of a Galerkin datum is integrable against `sinθcos²θ` for every `z > 0`. -/
theorem GalClass.slice_sinCos2_integrable {α : ℝ} {g : Fn} (hg : Work.FTS.Nonlin.GalClass α g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => g z θ * sg θ) Iθ :=
  Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 (GalClass.smoothOpen hg).continuousOn
    (GalClass.hkMem_zero hg) hz

/-! ## Slice integrability of the `ℋ⁴`-slots -/

/-- **The square of the angular slice** of an `ℋ⁴`-function is integrable: the `D_z⁰`-slot of
`HkIntegrand α 4 g` dominates `g²` on the open angle interval. -/
theorem slice_sq_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Iθ := by
  have hHs : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Iθ :=
    hmem.1 s (Set.mem_Ici.mpr hs.le)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => (g s θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcont hs).pow 2
  refine MeasureTheory.Integrable.mono' hHs haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := Real.rpow_pos_of_pos hsin _
  have hSle : S ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 2)]
    nlinarith
  have hA : 1 ≤ Work.Spaces.w s / S := by
    rw [le_div_iff₀ hSpos, one_mul]
    exact le_trans hSle hw1
  have hsq : (g s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  calc (g s θ) ^ 2 = (g s θ) ^ 2 * 1 := by ring
    _ ≤ (g s θ) ^ 2 * (Work.Spaces.w s / S) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [hA, hSpos]
    _ = (g s θ * (Work.Spaces.w s / S)) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hsq

/-- The slice `θ ↦ K(θ)·g(s,θ)/s` of the `L₁₂`-density is integrable for `s > 0`. -/
theorem L12dens_slice_integrable {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Kθ θ * g s θ / s) Iθ := by
  have hsq : MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Iθ :=
    slice_sq_integrable hcont hmem hs
  have hK : MeasureTheory.IntegrableOn (fun θ => (Kθ θ) ^ 2) Iθ :=
    ((Work.Elliptic.continuous_ktheta.pow 2).continuousOn).integrableOn_compact
      (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => ((Kθ θ) ^ 2 + (g s θ) ^ 2) / (2 * s)) Iθ :=
    (hK.add hsq).div_const (2 * s)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Kθ θ * g s θ / s)
      (MeasureTheory.volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Kθ p.2 * g p.1 p.2 / p.1)
      ((Work.Elliptic.continuous_ktheta.comp continuous_snd).continuousOn.mul hcont |>.div
        continuousOn_fst (fun _ hp => ne_of_gt hp.1)) hs
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hKnn : 0 ≤ Kθ θ := by
    rw [Work.Elliptic.Ktheta]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    positivity
  have hAM : 2 * (Kθ θ * |g s θ|) ≤ (Kθ θ) ^ 2 + (g s θ) ^ 2 := by
    nlinarith [sq_nonneg (Kθ θ - |g s θ|), sq_abs (g s θ)]
  rw [Real.norm_eq_abs, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * s)]
  have hval : |Kθ θ * g s θ / s| * (2 * s) = 2 * (Kθ θ * |g s θ|) := by
    rw [abs_div, abs_of_pos hs, abs_mul, abs_of_nonneg hKnn]
    field_simp
  rw [hval]
  exact hAM

/-! ## Linearity of the `L₁₂`-density and of `L₁₂` -/

/-- The density is additive (with a scalar) on integrable slices. -/
theorem L12dens_add_mul {f h : ℝ → ℝ → ℝ} {c s : ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => Kθ θ * f s θ / s) Iθ)
    (hh : MeasureTheory.IntegrableOn (fun θ => Kθ θ * h s θ / s) Iθ) :
    Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s := by
  rw [Work.Elliptic.L12dens, Work.Elliptic.L12dens, Work.Elliptic.L12dens,
    show (∫ θ in Iθ, Kθ θ * (f s θ + c * h s θ) / s)
        = ∫ θ in Iθ, (Kθ θ * f s θ / s + c * (Kθ θ * h s θ / s)) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_add hf (hh.const_mul c), MeasureTheory.integral_const_mul]

/-- The density is homogeneous (no integrability hypothesis). -/
theorem L12dens_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.Elliptic.L12dens (fun z θ => c * f z θ) s
      = c * Work.Elliptic.L12dens f s := by
  rw [Work.Elliptic.L12dens, Work.Elliptic.L12dens,
    show (∫ θ in Iθ, Kθ θ * (c * f s θ) / s)
        = ∫ θ in Iθ, c * (Kθ θ * f s θ / s) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by ring]
  rw [MeasureTheory.integral_const_mul]

/-- `L₁₂` is homogeneous in the profile (no integrability hypothesis). -/
theorem L12_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.L12 (fun z θ => c * f z θ) z = c * Work.Elliptic.L12 f z := by
  rw [Work.Elliptic.L12, Work.Elliptic.L12,
    show (fun r => Work.Elliptic.L12dens (fun z θ => c * f z θ) r)
        = fun r => c * Work.Elliptic.L12dens f r from
      funext fun r => L12dens_const_mul c f r]
  rw [MeasureTheory.integral_const_mul]

/-! ## Linearity of the orthogonalised source -/

/-- `orthSource` is additive (with a scalar), given the additivity of `F_*` at the radial
parameter `z`. -/
theorem orthSource_add_mul_apply {f h : ℝ → ℝ → ℝ} {c z θ : ℝ}
    (heq : Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Fstar f z + c * Work.Elliptic.Fstar h z) :
    Work.Elliptic.orthSource (fun z θ => f z θ + c * h z θ) z θ
      = Work.Elliptic.orthSource f z θ + c * Work.Elliptic.orthSource h z θ := by
  rw [Work.Elliptic.orthSource, Work.Elliptic.orthSource, Work.Elliptic.orthSource, heq]
  ring


/-! ## Congruence of `F_*` along agreement on the open angle interval -/

theorem Fstar_congr_Ioo {f h : ℝ → ℝ → ℝ} {z : ℝ}
    (hfh : ∀ θ, 0 < θ → θ < π / 2 → f z θ = h z θ) :
    Work.Elliptic.Fstar f z = Work.Elliptic.Fstar h z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  exact MeasureTheory.integral_congr_ae
    (Work.Elliptic.ae_restrict_Iθ_of_Ioo (p := fun θ => f z θ * sg θ = h z θ * sg θ)
      (fun θ h0 h1 => by rw [hfh θ h0 h1]))

end Work.FTS.EllSol
