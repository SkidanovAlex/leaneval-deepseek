/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.AeDataAof` — the twisted datum `(z²∂_z²Ψ, z²∂_z²F)` is a datum of the a.e. class

This module proves `Work.FTS.EllipticEst.H2W.AeDataAof`: for every datum `(F, Ψ)` of the weak
class `TT.EllWeakPos α 2 F Ψ` (the equation `bslOp α Ψ = F` on the open quadrant, the Dirichlet
data, the two moment conditions, smoothness of `Ψ` on the open quadrant and the three `ℋ²`
certificates of `F`, `z²∂_z²Ψ` and `∂_θ²Ψ`), the *twisted* pair

  `(A Ψ, G F) = (z²∂_z²Ψ,  D_z²F − D_zF) = (z²∂_z²Ψ,  z²∂_z²F)`

belongs to the almost-everywhere class `H2W.Ae.AeData` of the level-`0` elliptic estimate.  It is
the closure property that lets the radial second-order estimate be applied to the radially
differentiated data.

## The fields of `AeData`, and where each comes from

Writing `A := z²∂_z²Ψ` and `G := z²∂_z²F`:

* `0 < α`, `α ≤ 1/4`: the two hypotheses (the statement carries `hα`, `hα4`).
* the equation `bslOp α A = G` on the open quadrant: by the locality of `bslOp α` on the open
  quadrant and the identity `A = D_z²Ψ − D_zΨ` there, `bslOp α A = bslOp α (D_z²Ψ) −
  bslOp α (D_zΨ)`, which is `D_z²F − D_zF = G` by the radially differentiated equations
  (`bslOp_DzIter_eq`).
* the Dirichlet data `A z 0 = A z (π/2) = 0`: the `θ = 0` (resp. `θ = π/2`) slice of `Ψ`
  vanishes identically, hence so does that slice of every `z`-derivative, in particular
  `∂_z²Ψ`.
* smoothness of `A` on the open quadrant: `z²` times a `z`-iterate of the smooth `Ψ`
  (`remov.smoothOpen_slices_weak`).
* `G ∈ ℋ⁰`, `z²∂_z²A ∈ ℋ⁰` and `∂_θ²A ∈ ℋ⁰`: the first two are the `ℋ⁰`-membership of
  `z²∂_z²` of a function of `ℋ²` (`HkMem_zero_zsq_pzIter2`, applied to `F` resp. to `A`); the
  third is `∂_θ²A = z²∂_z²(∂_θ²Ψ)` together with `HkMem α 2 (∂_θ²Ψ)`
  (`HkMem_zero_pthIter2_zsq_pzIter2`).
* the two moment conditions `F_* A = 0` and `F_* G = 0` a.e.: the first is
  `F_*A(z) = F_*(D_z²Ψ)(z) − F_*(D_zΨ)(z) = 0` a.e., the second is
  `F_*G(z) = F_*(D_z²F)(z) − F_*(D_zF)(z) = 0` a.e.; both come from the *radial moment chain*
  `F_*(D_z^jΨ)(z) − F_*(D_z^jΨ)(s) = ∫_s^z F_*(D_z^{j+1}Ψ)(r)/r dr` (`Fstar_DzIter_Psi_ae`,
  `Fstar_DzIter_F_ae`).

## The local library

The pieces that this module needs are proved (or reproduced) here, so that it depends only on
the `OpenQDefs`/`OpenQAux` layer, on the clean moment-chain modules
(`Fstar_sub_eq_integral_pz`, `Cert.GbarSin.FstarDzIter_chain_open`, `AeBasic`), on the
one-dimensional slice estimate `Mine.SliceMomentTaylor` (the source of the `L¹` control of the
angular slices of `D_z^iΨ`, which are *not* bounded functions of the class) and on
`remov.smoothOpen_slices_weak`:

* `zsq_pzIter2_eq_open`, `pthIter_two_zsq_pzIter2_eq`, `bslOp_congr_Q0`: the operator identities
  on the open quadrant;
* the `ℋ⁰`-tools `HkIntegrand_zero_eq`, `HkMem_zero_of_majorant`, `excess_zsummand_mem`,
  `HkMem_zero_congr`;
* the slice/box machinery for the moment chain of `Ψ`: `slot`, `Bnd`, `slice_bound`,
  `Bnd_integrableOn`, `integrableUncurryDivOfFibreBound`, `integrable_box_pz_DzIter`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.Level0ADefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.bslOp_sub
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.Mine.SliceMomentTaylor
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace AeDataAofAux

/-! ## §1 The operator identities on the open quadrant -/

/-- `∂_θ^i f` is `C^∞` on the open quadrant when `f` is. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Multiplication of a `SmoothOpen` function by the polynomial `z²` stays `SmoothOpen`. -/
theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => z ^ 2 * g z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry g := by funext p; rfl
  rw [hfun]
  exact (contDiffOn_fst.pow 2).mul hg

/-- **`z²∂_z²f = D_z²f − D_zf`** at every point of the open quadrant, for `f` which is `C^∞`
there. -/
theorem zsq_pzIter2_eq_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ := by
  have hfd : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz f z' θ)
      (Work.Spaces.pz f z θ + z * Work.Spaces.pzIter 2 f z θ) z := by
    have h1 : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz f z' θ)
        (Work.Spaces.pzIter 2 f z θ) z := by
      have h := hf.hasDerivAt_slice_pzIter 1 hθ hz
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
    have h := h1.mul h2
    convert h using 1
    ring
  have hDz : Work.Spaces.DzIter 1 f z θ = z * Work.Spaces.pz f z θ := rfl
  have hD2 : Work.Spaces.DzIter 2 f z θ
      = z * deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z := rfl
  rw [hDz, hD2, hfd.deriv]
  ring

/-- On the open quadrant, `∂_θ^m` commutes with `∂_z`. -/
theorem pz_pthIter_comm_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter m g)))
      (Function.uncurry (Work.Spaces.pthIter m (Work.Spaces.pz g)))
        Work.FTS.EllipticEst.Q0 := by
  induction m with
  | zero => intro p hp; rfl
  | succ k ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter k g)) (z, θ) :=
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pthIter k g)).mp
          (smoothOpen_pthIter hg k) 2).contDiffAt
            (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hpt)
      have hstep : Work.Spaces.pz (Work.Spaces.pthIter (k + 1) g) z θ
          = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter k g)) z θ := by
        rw [Work.Spaces.pthIter_succ]
        exact Work.Spaces.pz_pth_comm hcd
      have hstep2 : Work.Spaces.pthIter (k + 1) (Work.Spaces.pz g) z θ
          = Work.Spaces.pth (Work.Spaces.pthIter k (Work.Spaces.pz g)) z θ := by
        rw [Work.Spaces.pthIter_succ]
      change Work.Spaces.pz (Work.Spaces.pthIter (k + 1) g) z θ
        = Work.Spaces.pthIter (k + 1) (Work.Spaces.pz g) z θ
      rw [hstep, hstep2]
      exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hpt

/-- On the open quadrant, `∂_θ^m` commutes with `∂_z^j`. -/
theorem pthIter_pzIter_comm_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter m (Work.Spaces.pzIter j g)))
      (Function.uncurry (Work.Spaces.pzIter j (Work.Spaces.pthIter m g)))
        Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ k ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hle : Work.Spaces.pthIter m (Work.Spaces.pz (Work.Spaces.pzIter k g)) z θ
          = Work.Spaces.pz (Work.Spaces.pthIter m (Work.Spaces.pzIter k g)) z θ :=
        (pz_pthIter_comm_Q0 (hg.pzIter k) m hpt).symm
      have hpz : Work.Spaces.pz (Work.Spaces.pthIter m (Work.Spaces.pzIter k g)) z θ
          = Work.Spaces.pz (Work.Spaces.pzIter k (Work.Spaces.pthIter m g)) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hpt
      change Work.Spaces.pthIter m (Work.Spaces.pzIter (k + 1) g) z θ
        = Work.Spaces.pzIter (k + 1) (Work.Spaces.pthIter m g) z θ
      rw [show Work.Spaces.pzIter (k + 1) g = Work.Spaces.pz (Work.Spaces.pzIter k g) from rfl,
        show Work.Spaces.pzIter (k + 1) (Work.Spaces.pthIter m g)
            = Work.Spaces.pz (Work.Spaces.pzIter k (Work.Spaces.pthIter m g)) from rfl,
        hle, hpz]

/-- A coefficient depending only on `z` passes through the iterated `θ`-derivatives. -/
theorem pthIter_fst_mul (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (m : ℕ) :
    Work.Spaces.pthIter m (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.pthIter m g z θ := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      show deriv (fun θ' => c z * Work.Spaces.pthIter k g z θ') θ
        = c z * deriv (fun θ' => Work.Spaces.pthIter k g z θ') θ
      rw [deriv_const_mul_field]

/-- **`∂_θ²(z²∂_z²Ψ) = z²∂_z²(∂_θ²Ψ)`** on the open quadrant. -/
theorem pthIter_two_zsq_pzIter2_eq {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h2 : Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ :=
    congrFun (congrFun (pthIter_fst_mul (fun z : ℝ => z ^ 2)
      (Work.Spaces.pzIter 2 Ψ) 2) z) θ
  have h3 : Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ
      = Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    pthIter_pzIter_comm_Q0 hΨ 2 2 hpt
  rw [h2, h3]

/-! ## §2 The level-`0` `ℋ`-integrand -/

/-- `HkIntegrand α 0 f` is the weighted square of `f`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- The `ℋ⁰`-integrand vanishes at `z = 0`. -/
theorem HkIntegrand_zero_z {α : ℝ} (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f 0 θ = 0 := by
  rw [HkIntegrand_zero_eq]
  simp [Work.Spaces.w]

/-- The `ℋ⁰`-integrand vanishes at `θ = 0`. -/
theorem HkIntegrand_zero_theta_zero {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [HkIntegrand_zero_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- The `ℋ⁰`-integrand vanishes at `θ = π/2`. -/
theorem HkIntegrand_zero_theta_pi {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [HkIntegrand_zero_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- **`ℋ⁰`-membership by a pointwise majorant.** -/
theorem HkMem_zero_of_majorant {α : ℝ} {f M : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMsl : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkMem α 0 f := by
  have hC : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
        = fun p : ℝ × ℝ => (f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      exact HkIntegrand_zero_eq α f p.1 p.2
    rw [hfun]
    exact (hf.mul (Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  refine Work.Blocks.HkMem_of_majorant_aesm (α := α) (k := 0) (f := f) (M := M)
    ?_ ?_ hMsl hMz hle
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine (MeasureTheory.aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      exact (HkIntegrand_zero_z (α := α) f θ).symm
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hC hz0
  · exact (Work.Spaces.aesm_of_continuousOn_Qd _ hC).integral_prod_right'

/-- **A single radial summand of an honest `ℋ^k`-integrand is honest in `ℋ⁰`.** -/
theorem excess_zsummand_mem (α : ℝ) (k i : ℕ) (f : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) (hi : i ≤ k) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f) := by
  refine HkMem_zero_of_majorant (α := α) (f := Work.Spaces.DzIter i f)
    (M := fun z θ => Work.Spaces.HkIntegrand α k f z θ) hcont (fun z hz => hmem.1 z hz)
    hmem.2 ?_
  intro z hz θ hθ
  rw [HkIntegrand_zero_eq]
  exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi

/-- **`ℋ⁰`-membership transfers along an identity on the open quadrant.** -/
theorem HkMem_zero_congr {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.Spaces.HkMem α 0 g) :
    Work.Spaces.HkMem α 0 f := by
  refine HkMem_zero_of_majorant (α := α) (f := f)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 g z θ) hf ?_ ?_ ?_
  · intro z hz
    exact (hg.1 z hz).const_mul 2
  · have h' := hg.2.const_mul 2
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_z]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ)
    · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ0
      · rw [← hθ_eq, HkIntegrand_zero_theta_zero]
        exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g z 0)
      · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ1
        · rw [hθ_eq, HkIntegrand_zero_theta_pi]
          exact mul_nonneg (by norm_num)
            (Work.Spaces.HkIntegrand_nonneg α 0 g z (Real.pi / 2))
        · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, h z θ hz0 hθ0 hθ1]
          nlinarith [sq_nonneg (g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

/-- **`z²∂_z²X ∈ ℋ⁰` from `X ∈ ℋ²`.** -/
theorem HkMem_zero_zsq_pzIter2 (α : ℝ) {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hmem : Work.Spaces.HkMem α 2 X) :
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) := by
  have hz2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 X) :=
    excess_zsummand_mem α 2 2 X (hX.DzIter 2).continuousOn hmem le_rfl
  have hz1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 X) :=
    excess_zsummand_mem α 2 1 X (hX.DzIter 1).continuousOn hmem (by norm_num)
  have hMnn : ∀ z θ, (0 : ℝ)
      ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 X) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 X) z θ := by
    intro z θ
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 2 X) z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 1 X) z θ
    linarith
  refine HkMem_zero_of_majorant
    (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 X) z θ
      + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 X) z θ)
    (smoothOpen_zsq_mul (hX.pzIter 2)).continuousOn ?_ ?_ ?_
  · intro z hz
    exact ((hz2.1 z hz).const_mul 2).add ((hz1.1 z hz).const_mul 2)
  · have h' := (hz2.2.const_mul 2).add (hz1.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((hz2.1 z hz).const_mul 2)
      ((hz1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_z]
      exact hMnn 0 θ
    · rcases eq_or_lt_of_le hθ.1 with hθ0_eq | hθ0
      · rw [← hθ0_eq, HkIntegrand_zero_theta_zero]
        exact hMnn z 0
      · rcases eq_or_lt_of_le hθ.2 with hθ1_eq | hθ1
        · rw [hθ1_eq, HkIntegrand_zero_theta_pi]
          exact hMnn z (Real.pi / 2)
        · have hid : z ^ 2 * Work.Spaces.pzIter 2 X z θ
              = Work.Spaces.DzIter 2 X z θ - Work.Spaces.DzIter 1 X z θ :=
            zsq_pzIter2_eq_open hX hz0 ⟨hθ0, hθ1⟩
          set A : ℝ := Work.Spaces.DzIter 2 X z θ with hAdef
          set B : ℝ := Work.Spaces.DzIter 1 X z θ with hBdef
          set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            with hWdef
          have hL : Work.Spaces.HkIntegrand α 0
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ) z θ = ((A - B) * W) ^ 2 := by
            rw [HkIntegrand_zero_eq, hid]
          have hA2 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 X) z θ = (A * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 2 X) z θ
          have hB1 : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 X) z θ = (B * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 1 X) z θ
          rw [hL, hA2, hB1]
          nlinarith [sq_nonneg (A * W + B * W)]

/-- **`∂_θ²(z²∂_z²Ψ) ∈ ℋ⁰`** from the honesty of `∂_θ²Ψ` at level `2`. -/
theorem HkMem_zero_pthIter2_zsq_pzIter2 {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter hΨ 2
  have hz2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
    excess_zsummand_mem α 2 2 (Work.Spaces.pthIter 2 Ψ)
      ((hBsm.DzIter 2).continuousOn) hmemB le_rfl
  have hz1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
    excess_zsummand_mem α 2 1 (Work.Spaces.pthIter 2 Ψ)
      ((hBsm.DzIter 1).continuousOn) hmemB (by norm_num)
  have hcont : ContinuousOn
      (Function.uncurry (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hbase : ContinuousOn
        (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_fst.pow 2).mul ((hBsm.pzIter 2).continuousOn)
    refine hbase.congr ?_
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
    exact pthIter_two_zsq_pzIter2_eq hΨ hz ⟨hθ0, hθ1⟩
  have hMnn : ∀ z θ, (0 : ℝ)
      ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ := by
    intro z θ
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0
      (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
    linarith
  change Work.Spaces.HkMem α 0
    (fun z θ => Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
  refine HkMem_zero_of_majorant (f := fun z θ =>
      Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
    (M := fun z θ =>
      2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ) hcont ?_ ?_ ?_
  · intro z hz
    exact ((hz2.1 z hz).const_mul 2).add ((hz1.1 z hz).const_mul 2)
  · have h' := (hz2.2.const_mul 2).add (hz1.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((hz2.1 z hz).const_mul 2)
      ((hz1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_z]
      exact hMnn 0 θ
    · rcases eq_or_lt_of_le hθ.1 with hθ0_eq | hθ0
      · rw [← hθ0_eq, HkIntegrand_zero_theta_zero]
        exact hMnn z 0
      · rcases eq_or_lt_of_le hθ.2 with hθ1_eq | hθ1
        · rw [hθ1_eq, HkIntegrand_zero_theta_pi]
          exact hMnn z (Real.pi / 2)
        · have hid : Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              = Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
                - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ := by
            rw [pthIter_two_zsq_pzIter2_eq hΨ hz0 ⟨hθ0, hθ1⟩,
              zsq_pzIter2_eq_open hBsm hz0 ⟨hθ0, hθ1⟩]
          set A : ℝ := Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ with hAdef
          set B : ℝ := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ with hBdef
          set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            with hWdef
          have hL : Work.Spaces.HkIntegrand α 0
                (fun z θ => Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) z θ
              = ((A - B) * W) ^ 2 := by
            rw [HkIntegrand_zero_eq, hid]
          have hA2 : Work.Spaces.HkIntegrand α 0
                (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ = (A * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
          have hB1 : Work.Spaces.HkIntegrand α 0
                (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ = (B * W) ^ 2 :=
            HkIntegrand_zero_eq α (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
          rw [hL, hA2, hB1]
          nlinarith [sq_nonneg (A * W + B * W)]

/-! ## §3 The equation of the twisted datum -/

/-- `bslOp α` is local on the open quadrant. -/
theorem bslOp_congr_Q0 (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α f z θ = Work.Elliptic.bslOp α g z θ := by
  intro z θ hz hθ0 hθ1
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hEq : Set.EqOn (Function.uncurry f) (Function.uncurry g)
      Work.FTS.EllipticEst.Q0 := fun p hp =>
    h p.1 p.2 (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1 (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2
  have hpz1 : Work.Spaces.pz f z θ = Work.Spaces.pz g z θ :=
    Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hq
  have hpz2 : Work.Spaces.pzIter 2 f z θ = Work.Spaces.pzIter 2 g z θ := by
    have hEq2 : Set.EqOn (Function.uncurry (Work.Spaces.pz f))
        (Function.uncurry (Work.Spaces.pz g)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hp
    exact Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq2 hq
  have hpth2 : Work.Spaces.pthIter 2 f z θ = Work.Spaces.pthIter 2 g z θ := by
    have hEq2 : Set.EqOn (Function.uncurry (Work.Spaces.pth f))
        (Function.uncurry (Work.Spaces.pth g)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hp
    exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq2 hq
  have htan : Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ := by
    refine Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ?_ hq
    intro p hp
    obtain ⟨ha, hb0, hb1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    simp only [Function.uncurry]
    rw [h p.1 p.2 ha hb0 hb1]
  have hpt : f z θ = g z θ := h z θ hz hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, hpz2, hpz1, hpth2, htan, hpt]

/-- **The equation of the twisted datum**: `bslOp α (z²∂_z²Ψ) = D_z²F − D_zF` on the open
quadrant. -/
theorem bslOp_Aof_eq_Gof (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Aof Ψ) z θ = Gof F z θ := by
  intro z hz θ hθ0 hθ1
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter 2 Ψ)) (z, θ) :=
    ((hΨ.DzIter 2).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  have hcd1 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 Ψ)) (z, θ) :=
    ((hΨ.DzIter 1).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hloc : Work.Elliptic.bslOp α (Aof Ψ) z θ
      = Work.Elliptic.bslOp α
          (fun z θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) z θ :=
    bslOp_congr_Q0 α (fun a b ha hb0 hb1 => zsq_pzIter2_eq_open hΨ ha ⟨hb0, hb1⟩)
      z θ hz hθ0 hθ1
  have hlin := Work.FTS.EllipticEst.bslOp_sub α (Work.Spaces.DzIter 2 Ψ)
    (Work.Spaces.DzIter 1 Ψ) z θ hcos hcd2 hcd1
  have hE2 := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 2 h.smooth h.eq z hz θ hθ0 hθ1
  have hE1 := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.eq z hz θ hθ0 hθ1
  show Work.Elliptic.bslOp α (Aof Ψ) z θ
    = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
  rw [hloc, hlin, hE2, hE1]

/-! ## §4 The boundary slices of the radial derivatives -/

/-- If the `θ = a` slice of `Ψ` vanishes identically, then so does the `θ = a` slice of
`∂_z²Ψ`. -/
theorem pzIter_two_eq_zero_of_slice_zero {Ψ : ℝ → ℝ → ℝ} {a : ℝ} (ha : ∀ z, Ψ z a = 0) :
    ∀ z, Work.Spaces.pzIter 2 Ψ z a = 0 := by
  have h1 : ∀ z, Work.Spaces.pz Ψ z a = 0 := by
    intro z
    have hfun : (fun z' : ℝ => Ψ z' a) = fun _ => (0 : ℝ) := funext fun z' => ha z'
    have hz : Work.Spaces.pz Ψ z a = deriv (fun z' : ℝ => Ψ z' a) z := rfl
    rw [hz, hfun]
    simp
  intro z
  have hfun : (fun z' : ℝ => Work.Spaces.pz Ψ z' a) = fun _ => (0 : ℝ) := funext h1
  have hz : Work.Spaces.pzIter 2 Ψ z a = deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' a) z := rfl
  rw [hz, hfun]
  simp

/-! ## §5 Pointwise facts about the angular weights -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hθ.1]) hθ.2
  simp only [Work.Elliptic.sinCos2]
  positivity

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

theorem integrableOn_sinCos2_Iθ : IntegrableOn Work.Elliptic.sinCos2 Work.Spaces.Iθ :=
  continuous_sinCos2.continuousOn.integrableOn_compact isCompact_Icc

theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- The pointwise energy/slot comparison. -/
theorem sq_mul_sEta_le_slot {D z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (D * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq D (Work.Spaces.w z) hθ]
  have hse : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := sEta_nonneg hθ
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith [one_le_w hz]
  calc D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.w z) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg D)
        calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 1 := by ring
          _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 :=
              mul_le_mul_of_nonneg_left hw2 hse
    _ = D ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## §6 The Taylor majorant for the angular slices of `D_z^i Ψ` -/

/-- The weighted `ℋ²`-slot of `g` at the radius `u`. -/
def slot (g : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ
    * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

theorem slot_nonneg (g : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : 0 ≤ slot g i u :=
  integral_nonneg fun θ => sq_nonneg _

/-- The `u`-slice of a function `C^∞` on the open quadrant is `C²` on `(0,π/2)`. -/
theorem contDiffOn_slice_two {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) :
    ContDiffOn ℝ 2 (fun θ : ℝ => g u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hg.curry_θ hu).of_le (by simp [Work.Stability.smoothOrder])

theorem continuousOn_sin_rpow_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem aesm_energy_slice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ)
    {u : ℝ} (hu : 0 < u) :
    AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
    (((hg.DzIter i).continuousOn).pow 2 |>.mul continuousOn_sin_rpow_Q0) hu

/-- The `η`-weighted energy of a single radial summand of `g` is dominated by its `ℋ²`-slot. -/
theorem energy_le_slot_aux {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 g) (i : ℕ) (hi : i ≤ 2) {u : ℝ} (hu : 0 < u) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot g i u := by
  have hslot := Work.FTS.EllipticEst.integrableOn_zSummand α 2 hg hB i hi
    (Set.mem_Ici.mpr hu.le)
  have henergy : IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    Integrable.mono' hslot (aesm_energy_slice hg i hu) (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))]
      exact sq_mul_sEta_le_slot hθ hu)
  refine integral_mono_ae henergy hslot ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact sq_mul_sEta_le_slot hθ hu

/-- The `∂_θ²`-energy integrand of the slice `D_z^i Ψ` is integrable, `i ≤ 2`. -/
theorem integrableOn_pthIter2_slice {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hpt_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ
        = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ :=
    fun θ hθ => Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i
      (show (u, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
  have hae : (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ
    rw [hθ]
  refine Integrable.mono'
    (Work.FTS.EllipticEst.integrableOn_zSummand α 2 ((hΨ.pth).pth) hB i hi
      (Set.mem_Ici.mpr hu.le)) ?_ ?_
  · exact (aesm_energy_slice ((hΨ.pth).pth) i hu).congr hae.symm
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ hθeq
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)), hθeq]
    exact sq_mul_sEta_le_slot hθ hu

/-- The `∂_θ²`-energy of the slice `D_z^i Ψ` is bounded by the `ℋ²`-slot of `∂_θ²Ψ`. -/
theorem energy_pthIter2_le_slot {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot (Work.Spaces.pthIter 2 Ψ) i u := by
  have hpt_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ
        = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ :=
    fun θ hθ => Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i
      (show (u, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
  have hae : (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ
    rw [hθ]
  refine le_trans (le_of_eq ?_) (energy_le_slot_aux ((hΨ.pth).pth) hB i hi hu)
  exact integral_congr_ae hae

/-- The majorant of `∫_θ |D_z^i Ψ(u,θ)| sinθcos²θ` delivered by the slice Taylor estimate. -/
def Bnd (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1)

theorem Bnd_nonneg (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : 0 ≤ Bnd Ψ i u := by
  rw [Bnd]
  have h := slot_nonneg (Work.Spaces.pthIter 2 Ψ) i u
  have h1 := abs_nonneg (Work.Spaces.DzIter i Ψ u (Real.pi / 4))
  have h2 := abs_nonneg (Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4))
  linarith

/-- **The angular slice bound** for `D_z^i Ψ`, `i ≤ 2`. -/
theorem slice_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u : ℝ, 0 < u →
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ
        ≤ Bnd Ψ i u := by
  intro u hu
  have hE := integrableOn_pthIter2_slice hΨ hB i hi hu
  obtain ⟨-, hbound⟩ := Work.FTS.EllipticEst.Mine.SliceMomentTaylor
    (contDiffOn_slice_two (hΨ.DzIter i) hu) hE
  have hsqrt : Real.sqrt (∫ θ in Work.Spaces.Iθ,
        deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot (Work.Spaces.pthIter 2 Ψ) i u + 1 := by
    have henergy : (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ slot (Work.Spaces.pthIter 2 Ψ) i u :=
      energy_pthIter2_le_slot hΨ hB i hi hu
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ Real.sqrt (slot (Work.Spaces.pthIter 2 Ψ) i u) := Real.sqrt_le_sqrt henergy
      _ ≤ slot (Work.Spaces.pthIter 2 Ψ) i u + 1 := by
          have h := slot_nonneg (Work.Spaces.pthIter 2 Ψ) i u
          nlinarith [Real.sq_sqrt h, sq_nonneg (Real.sqrt (slot (Work.Spaces.pthIter 2 Ψ) i u))]
  have hd1 : Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)
      = deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ) (Real.pi / 4) := rfl
  rw [Bnd]
  rw [← hd1] at hbound
  linarith [hbound, hsqrt]

/-- `Bnd Ψ i` is integrable on `(a,b] ⊂ (0,∞)`. -/
theorem Bnd_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd Ψ i) (Set.Ioc a b) := by
  have h4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hsub2 : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have h1 : IntegrableOn (fun u : ℝ => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|)
      (Set.Icc a b) :=
    (((hΨ.DzIter i).curry_z h4).continuousOn.mono hsub).abs.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun u : ℝ => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|)
      (Set.Icc a b) :=
    ((((hΨ.DzIter i).pth).curry_z h4).continuousOn.mono hsub).abs.integrableOn_compact
      isCompact_Icc
  have h3 : IntegrableOn (slot (Work.Spaces.pthIter 2 Ψ) i) (Set.Icc a b) :=
    (Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 ((hΨ.pth).pth) hB i hi).mono_set
      (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1))
  have hsum : IntegrableOn (fun u : ℝ => 3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1)) (Set.Ioc a b) :=
    (((h1.mono_set hsub2).const_mul 3).add ((h2.mono_set hsub2).const_mul 9)).add
      (((h3.mono_set hsub2).add (integrableOn_const (by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))).const_mul 9)
  have hEq : Bnd Ψ i = fun u : ℝ => 3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1) := rfl
  rw [hEq]
  exact hsum

/-- **Integrability of a divided fibre bound** (Tonelli from a fibre bound). -/
theorem integrableUncurryDivOfFibreBound {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {s z : ℝ}
    (hs : 0 < s) (hsz : s ≤ z)
    (hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)))
    (hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ => f r θ) Work.Spaces.Iθ)
    (hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Work.Spaces.Iθ, |f r θ| ≤ B r)
    (hB : IntegrableOn B (Set.Ioc s z)) :
    Integrable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  haveI : SFinite (volume.restrict (Set.Ioc s z)) := inferInstance
  haveI : SFinite (volume.restrict Work.Spaces.Iθ) := inferInstance
  have hG : Integrable (Function.uncurry (fun r θ : ℝ => |f r θ / r|))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated (μ := volume.restrict (Set.Ioc s z))
      (ν := volume.restrict Work.Spaces.Iθ) (G := fun r θ => |f r θ / r|)
      (fun a b => abs_nonneg _) ?_ ?_ ?_).1
    · exact hae.norm.congr (Filter.Eventually.of_forall fun p => by
        simp only [Function.uncurry, Real.norm_eq_abs])
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hr0 : 0 < r := lt_trans hs hr.1
      exact (((hfib r hr).norm.const_mul r⁻¹).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hr0)]
          ring))
    · refine (hB.const_mul s⁻¹).mono' ?_ ?_
      · exact (hae.norm.integral_prod_right'
          (μ := volume.restrict (Set.Ioc s z)) (ν := volume.restrict Work.Spaces.Iθ)).congr
          (Filter.Eventually.of_forall fun r => by
            simp only [Function.uncurry, Real.norm_eq_abs])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
        have hr0 : 0 < r := lt_trans hs hr.1
        have hBnn : 0 ≤ B r := le_trans (integral_nonneg fun θ => abs_nonneg _) (hle r hr)
        rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
        have h1 : ∫ θ in Work.Spaces.Iθ, |f r θ / r| = (∫ θ in Work.Spaces.Iθ, |f r θ|) / r := by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
          rw [abs_div, abs_of_pos hr0]
        rw [h1]
        have hstep1 : (∫ θ in Work.Spaces.Iθ, |f r θ|) / r ≤ B r / r :=
          div_le_div_of_nonneg_right (hle r hr) (le_of_lt hr0)
        have hstep2 : B r / r ≤ s⁻¹ * B r := by
          rw [div_eq_mul_inv, mul_comm (B r)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs (le_of_lt hr.1)) hBnn
        linarith
  refine (MeasureTheory.integrable_norm_iff hae).mp ?_
  exact hG.congr (Filter.Eventually.of_forall fun p => by
    simp only [Function.uncurry, Real.norm_eq_abs])

/-- The box integrability of `∂_z(D_z^a Ψ)·sinθcos²θ`, `a ≤ 1`. -/
theorem integrable_box_pz_DzIter {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (a : ℕ) (ha : a ≤ 1)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Integrable (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have ha2 : a + 1 ≤ 2 := by omega
  have hfib : ∀ r ∈ Set.Ioc s z,
      IntegrableOn (fun θ => Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
    intro r hr
    have hr0 : 0 < r := lt_trans hs hr.1
    exact (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
      (contDiffOn_slice_two (hΨ.DzIter (a + 1)) hr0)
      (integrableOn_pthIter2_slice hΨ hB (a + 1) ha2 hr0)).1
  have hle : ∀ r ∈ Set.Ioc s z,
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ|
        ≤ Bnd Ψ (a + 1) r := by
    intro r hr
    have hr0 : 0 < r := lt_trans hs hr.1
    have h := slice_bound hΨ hB (a + 1) ha2 r hr0
    refine le_trans (le_of_eq ?_) h
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]
  have hBint : IntegrableOn (Bnd Ψ (a + 1)) (Set.Ioc s z) :=
    Bnd_integrableOn hΨ hB (a + 1) ha2 hs
  have hae : AEStronglyMeasurable
      (Function.uncurry (fun r θ : ℝ =>
        (Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ) / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (a + 1) Ψ p.1 p.2
        * Work.Elliptic.sinCos2 p.2) / p.1) ?_).mono_measure ?_
    · refine ContinuousOn.div ?_ continuousOn_fst (fun p hp =>
        ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
      exact (((hΨ.DzIter (a + 1)).forall 0).continuousOn).mul
        (continuous_sinCos2.comp continuous_snd).continuousOn
    · rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
      exact MeasureTheory.Measure.restrict_mono
        (Set.prod_mono (fun r hr => le_of_lt (lt_trans hs hr.1)) subset_rfl) le_rfl
  have hdiv := integrableUncurryDivOfFibreBound (f := fun r θ =>
      Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ)
    (B := Bnd Ψ (a + 1)) hs hsz hae hfib hle hBint
  refine hdiv.congr ?_
  have hbox : ∀ᵐ p ∂((volume.restrict (Set.Ioc s z)).prod
      (volume.restrict Work.Spaces.Iθ)), p ∈ Set.Ioc s z ×ˢ Work.Spaces.Iθ := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.self_mem_ae_restrict (measurableSet_Ioc.prod measurableSet_Icc)
  filter_upwards [hbox] with p hp
  obtain ⟨r, θ⟩ := p
  obtain ⟨hr, -⟩ := hp
  have hr0 : 0 < r := lt_trans hs hr.1
  have hpz : Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
      = Work.Spaces.DzIter (a + 1) Ψ r θ / r := by
    show Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
      = Work.Spaces.Dz (Work.Spaces.DzIter a Ψ) r θ / r
    simp only [Work.Spaces.Dz]
    field_simp
  simp only [Function.uncurry, Function.uncurry_apply_pair, hpz]
  ring

/-! ## §7 The angular moment chain for `Ψ` -/

/-- `F_*(∂_z(D_z^a Ψ))(r) = F_*(D_z^{a+1}Ψ)(r)/r` for `r > 0`. -/
theorem Fstar_pz_DzIter_eq (Ψ : ℝ → ℝ → ℝ) (a : ℕ) {r : ℝ} (hr : 0 < r) :
    Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter a Ψ)) r
      = Work.Elliptic.Fstar (Work.Spaces.DzIter (a + 1) Ψ) r / r := by
  have hfun : (fun θ : ℝ => Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
        * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => (1 / r)
          * (Work.Spaces.DzIter (a + 1) Ψ r θ * Work.Elliptic.sinCos2 θ) := by
    funext θ
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
        = Work.Spaces.DzIter (a + 1) Ψ r θ / r := by
      show Work.Spaces.pz (Work.Spaces.DzIter a Ψ) r θ
        = Work.Spaces.Dz (Work.Spaces.DzIter a Ψ) r θ / r
      simp only [Work.Spaces.Dz]
      field_simp
    rw [hpz]
    ring
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, hfun, MeasureTheory.integral_const_mul]
  ring

/-- **The radial moment chain for `Ψ`**: `F_*(D_z^aΨ)(z) − F_*(D_z^aΨ)(s) =
∫_s^z F_*(D_z^{a+1}Ψ)(r)/r dr`, for `a ≤ 1`. -/
theorem Fstar_DzIter_tower_Psi {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {a : ℕ} (ha : a ≤ 1)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter a Ψ) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter a Ψ) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (a + 1) Ψ) r / r := by
  have hsl : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun θ => Work.Spaces.DzIter a Ψ x θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro x hx
    exact (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
      (contDiffOn_slice_two (hΨ.DzIter a) hx)
      (integrableOn_pthIter2_slice hΨ hB a (by omega) hx)).1
  have h := Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz (f := Work.Spaces.DzIter a Ψ)
    (hΨ.DzIter a) hs hsz (hsl s hs) (hsl z (lt_of_lt_of_le hs hsz))
    (integrable_box_pz_DzIter hΨ hB a ha hs hsz)
  rw [h]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr0 : 0 < r := by
    rw [Set.uIcc_of_le hsz] at hr
    exact lt_of_lt_of_le hs hr.1
  exact Fstar_pz_DzIter_eq Ψ a hr0

/-- **The angular moments of `D_z^j Ψ` vanish a.e., `j ≤ 2`.** -/
theorem Fstar_DzIter_Psi_ae {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  -- the interval integrability of the divided moments
  have hInt : ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable
        (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r / r) volume a b := by
    intro j hj a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    have hBndI : MeasureTheory.IntegrableOn (Bnd Ψ j) (Set.Icc a b) :=
      (Bnd_integrableOn hΨ hB j hj ha).congr_set_ae
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm
    refine MeasureTheory.Integrable.mono' (hBndI.const_mul (1 / a)) ?_ ?_
    · -- a.e. strong measurability of the divided moment
      have hjoint : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.DzIter j Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _
          (((hΨ.DzIter j).forall 0).continuousOn.mul
            (continuous_sinCos2.comp continuous_snd).continuousOn)
      have hF : AEStronglyMeasurable
          (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r)
          (volume.restrict Work.Spaces.Iz) := by
        have h' := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
          (ν := volume.restrict Work.Spaces.Iθ)
        simpa only [Work.Elliptic.Fstar, Function.uncurry_apply_pair] using h'
      have hIcc : (volume.restrict (Set.Icc a b)) ≤ (volume.restrict Work.Spaces.Iz) :=
        MeasureTheory.Measure.restrict_mono
          (fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)) le_rfl
      have h2 : AEStronglyMeasurable
          (fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r * r⁻¹)
          (volume.restrict (Set.Icc a b)) :=
        (hF.mono_measure hIcc).mul (measurable_inv.aestronglyMeasurable :
          AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Set.Icc a b)))
      exact h2.congr (Filter.Eventually.of_forall fun r => div_eq_mul_inv _ _)
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with r hr
      have har : a ≤ r := hr.1
      have hrpos : 0 < r := lt_of_lt_of_le ha har
      have hb := slice_bound hΨ hB j hj r hrpos
      have hnorm : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r|
          ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter j Ψ r θ| * Work.Elliptic.sinCos2 θ := by
        rw [Work.Elliptic.Fstar]
        refine (MeasureTheory.norm_integral_le_integral_norm
          (fun θ : ℝ => Work.Spaces.DzIter j Ψ r θ * Work.Elliptic.sinCos2 θ)).trans ?_
        refine le_of_eq ?_
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hrpos]
      have hdiv : |Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) r| / r
          ≤ Bnd Ψ j r / r := div_le_div_of_nonneg_right (le_trans hnorm hb) (le_of_lt hrpos)
      have hdiv2 : Bnd Ψ j r / r ≤ (1 / a) * Bnd Ψ j r := by
        rw [div_eq_mul_inv, mul_comm (Bnd Ψ j r), one_div]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ ha har) (Bnd_nonneg Ψ j r)
      linarith
  -- the base case and the induction
  have h0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthPsi
  have hstep : ∀ j : ℕ, j ≤ 1 →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) z = 0 := by
    intro j hj hW
    have hraw := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
      (W := fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z)
      (V := fun r => Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) r / r)
      (fun s t hs hst => Fstar_DzIter_tower_Psi hΨ hB (by omega) hs hst) hW
      (fun a b ha hab => hInt (j + 1) (by omega) a b ha hab)
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  intro j hj
  interval_cases j
  · simpa using h0
  · exact hstep 0 (by norm_num) h0
  · exact hstep 1 (by norm_num) (hstep 0 (by norm_num) h0)

/-! ## §8 The angular moment chain for `F` -/

/-- `F_*(D_z²F − D_zF)(z) = F_*(D_z²F)(z) − F_*(D_zF)(z)` for `z > 0`. -/
theorem Fstar_DzIter_sub (α : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 2 F) {z : ℝ}
    (hz : 0 < z) :
    Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 F z θ
        - Work.Spaces.DzIter 1 F z θ) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z := by
  have hI1 := Work.FTS.EllipticEst.integrableOn_DzIter_mul_sinCos2 α 2 hF hmem 1
    (by norm_num) hz
  have hI2 := Work.FTS.EllipticEst.integrableOn_DzIter_mul_sinCos2 α 2 hF hmem 2
    (by norm_num) hz
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Work.Spaces.DzIter 2 F z θ * Work.Elliptic.sinCos2 θ
          - Work.Spaces.DzIter 1 F z θ * Work.Elliptic.sinCos2 θ from by
    funext θ; ring]
  rw [MeasureTheory.integral_sub hI2 hI1]

/-- **The angular moments of `D_z^j F` vanish a.e., `j ≤ 2`.** -/
theorem Fstar_DzIter_F_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  have hmem : Work.Spaces.HkMem α 2 F := h.memF
  have hInt : ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        volume a b := by
    intro j hj a b ha hab
    have h1 := Work.FTS.EllipticEst.integrableOn_Bmom_div α 2 hF hmem j hj a b ha hab
    have h2 : IntegrableOn
        (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r) (Set.Icc a b) :=
      h1.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => by
        show Work.FTS.EllipticEst.Bmom F j r / r
          = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r
        rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact h2
  have h0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar F z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthF
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
    have hraw := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar F)
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF
        hmem 0 (by norm_num) hs hst)
      h0 (hInt 1 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  have h2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
    have hraw := Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F))
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF
        hmem 1 (by norm_num) hs hst)
      h1 (hInt 2 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  intro j hj
  interval_cases j
  · simpa using h0
  · exact h1
  · exact h2

/-! ## §9 The two moment conditions of the twisted datum -/

/-- `F_*` only depends on the integrand a.e. in `θ`. -/
theorem Fstar_congr_ae {f g : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), f z θ = g z θ) :
    Work.Elliptic.Fstar f z = Work.Elliptic.Fstar g z := by
  show (∫ θ in Work.Spaces.Iθ, f z θ * Work.Elliptic.sinCos2 θ)
    = ∫ θ in Work.Spaces.Iθ, g z θ * Work.Elliptic.sinCos2 θ
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with θ hθ
  rw [hθ]

theorem Aof_Gof_moments (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Aof Ψ) z = 0) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Gof F) z = 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  constructor
  · -- `F_*(z²∂_z²Ψ) = F_*(D_z²Ψ) − F_*(D_zΨ) = 0` a.e.
    have hmom := Fstar_DzIter_Psi_ae h
    filter_upwards [hmom 2 (by norm_num), hmom 1 (by norm_num),
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz2 hz1 hzpos
    have hsl2 : IntegrableOn
        (fun θ => Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
        (contDiffOn_slice_two (hΨ.DzIter 2) hzpos)
        (integrableOn_pthIter2_slice hΨ hB 2 (by norm_num) hzpos)).1
    have hsl1 : IntegrableOn
        (fun θ => Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      (Work.FTS.EllipticEst.Mine.SliceMomentTaylor
        (contDiffOn_slice_two (hΨ.DzIter 1) hzpos)
        (integrableOn_pthIter2_slice hΨ hB 1 (by norm_num) hzpos)).1
    have hcongr : Work.Elliptic.Fstar (Aof Ψ) z
        = Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
            - Work.Spaces.DzIter 1 Ψ z θ) z :=
      Fstar_congr_ae (by
        filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
          (fun θ hθ => zsq_pzIter2_eq_open hΨ hzpos hθ)] with θ hθ
        show Aof Ψ z θ = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ
        rw [Aof_apply, hθ])
    have hsub : Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 Ψ z θ
          - Work.Spaces.DzIter 1 Ψ z θ) z
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z
          - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      rw [show (fun θ : ℝ => (Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ)
            * Work.Elliptic.sinCos2 θ)
          = fun θ : ℝ => Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ
              - Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ from by
        funext θ; ring]
      rw [MeasureTheory.integral_sub hsl2 hsl1]
    rw [hcongr, hsub, hz2, hz1, sub_self]
  · -- `F_*(z²∂_z²F) = F_*(D_z²F) − F_*(D_zF) = 0` a.e.
    have hmom := Fstar_DzIter_F_ae α F Ψ h
    filter_upwards [hmom 2 (by norm_num), hmom 1 (by norm_num),
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz2 hz1 hzpos
    have hcongr : Work.Elliptic.Fstar (Gof F) z
        = Work.Elliptic.Fstar (fun z θ => Work.Spaces.DzIter 2 F z θ
            - Work.Spaces.DzIter 1 F z θ) z := rfl
    rw [hcongr, Fstar_DzIter_sub α hF h.memF hzpos, hz2, hz1, sub_self]

end AeDataAofAux

/-! ## The target -/

/-- **The twisted datum `(z²∂_z²Ψ, z²∂_z²F)` is a datum of the a.e. class `AeData`.**
See the module docstring for the provenance of each field. -/
theorem AeDataAof (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α
      (Work.FTS.EllipticEst.H2W.Aof Ψ) (Work.FTS.EllipticEst.H2W.Gof F) := by
  obtain ⟨-, -, hAsm, -⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  obtain ⟨hmomA, hmomG⟩ := AeDataAofAux.Aof_Gof_moments α F Ψ h
  refine ⟨hα, hα4, AeDataAofAux.bslOp_Aof_eq_Gof α h, ?_, ?_, ?_, ?_, ?_, ?_,
    hmomA, hmomG⟩
  · -- `A Ψ` vanishes on the `θ = 0` line
    intro z
    show Work.FTS.EllipticEst.H2W.Aof Ψ z 0 = 0
    rw [Aof_apply, AeDataAofAux.pzIter_two_eq_zero_of_slice_zero (fun z => h.zero z) z,
      mul_zero]
  · -- `A Ψ` vanishes on the `θ = π/2` line
    intro z
    show Work.FTS.EllipticEst.H2W.Aof Ψ z (Real.pi / 2) = 0
    rw [Aof_apply, AeDataAofAux.pzIter_two_eq_zero_of_slice_zero (fun z => h.pi_half z) z,
      mul_zero]
  · -- smoothness of `A Ψ` on the open quadrant
    intro n
    exact hAsm.forall n
  · -- `G F ∈ ℋ⁰`
    have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
      (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
    have hz := AeDataAofAux.HkMem_zero_zsq_pzIter2 α hFsm h.memF
    refine AeDataAofAux.HkMem_zero_congr (f := Gof F)
      (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ) ?_ ?_ hz
    · exact ((hFsm.DzIter 2).continuousOn).sub ((hFsm.DzIter 1).continuousOn)
    · intro z θ hz0 hθ0 hθ1
      show Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
        = z ^ 2 * Work.Spaces.pzIter 2 F z θ
      exact (AeDataAofAux.zsq_pzIter2_eq_open hFsm hz0 ⟨hθ0, hθ1⟩).symm
  · -- `z²∂_z²(A Ψ) ∈ ℋ⁰`, from `A Ψ ∈ ℋ²`
    exact AeDataAofAux.HkMem_zero_zsq_pzIter2 α hAsm h.memA
  · -- `∂_θ²(A Ψ) ∈ ℋ⁰`
    exact AeDataAofAux.HkMem_zero_pthIter2_zsq_pzIter2
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) h.memB

end Work.FTS.EllipticEst.H2W
