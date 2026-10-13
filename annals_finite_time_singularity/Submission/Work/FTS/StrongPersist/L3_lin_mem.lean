/-
# `Work.FTS.StrongPersist.L3_lin_mem` — the `ℋ³` estimate for the linear part (`L3Data.lin`)

This is the `lin` field of the level-three operator package `L3Data` of the strong-solution
route (design `FTS_STRONG_ROUTE.md` §3, node S6): for `f` in the honest level-six class
`H6Adm α f` the linear part

  `linPart α f = -𝓛_Γ^T f = -(𝓛 f) + 𝓐·L₁₂(f) + Transport f - 𝓑·L₁₂(Transport f)(0)`

lies in `ℋ³` and its norm is controlled by the `ℋ⁴`-norm of `f`, with a constant independent
of `α ∈ (0,1]`:

  `|linPart α f|_{ℋ³} ≤ C₃ (1 + |f|_{ℋ⁴})⁴`.

The estimate is assembled from three independent pieces (`L3Defs.linPart_eq`):

* `locOp f = -(𝓛 f) + Transport f` — the local first-order part (`L3Aux.locOp_HkSq_le`);
* `AcR α · Mf f` — the nonlocal term, in which the `(z,θ)`-separated coefficient
  `AcR α = (2z/(1+z)²)(Γ/c)` multiplies the *radial* function `Mf f = L₁₂(f)`
  (`L3Aux.Acoef_Mf_le`);
* `BcR α · K0f f` — the projector correction, the `(z,θ)`-separated coefficient
  `BcR α = (Γ/c)(2z²/(1+z)³)` times the *constant* `K0f f = L₁₂(Transport f)(0)`, bounded by
  `|K0f f| ≤ C|f|_{ℋ⁴}` (`L3Aux.Transport_L12_zero_le`) and `|BcR α|_{ℋ³}² ≤ C`
  (`L3Aux.bcoef_gamCoef_le`); the product estimate is `proj_le` below.

The three pieces are *not* all smooth on the open quadrant — the nonlocal one is only as smooth
as `L₁₂ f` is (`C³`, from `HkMem α 4 f`), and `SmoothOpen` of it is **false** for honest data
(the same obstruction that refuted the earlier form of `L3Data.lin`, see
`Submission/Work/FTS/StrongPersist/NOTES_L3_lin_FALSE.md`).  The assembly therefore uses the
finite-smoothness closure `L3Aux.HkMem_HkSq_add3_le` (three summands, `C^k` on the open
quadrant) rather than the `C^∞`-based `HkMem_add_open`/`HkIntegrand_add_le_of_contDiffOn`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Defs
import Submission.Work.FTS.StrongPersist.L3Aux.locOp_HkSq_le
import Submission.Work.FTS.StrongPersist.L3Aux.Acoef_Mf_le
import Submission.Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.StrongPersist.L3Aux.HkMem_HkSq_add3_le
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.Uop_bound_reg
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The raw forms of the two separated coefficients -/

/-- The nonlocal coefficient `(2z/(1+z)²)·(Γ(θ)/c(α))`, in the form in which the delegated
piece estimates state it. -/
def AcR (α : ℝ) : Fn :=
  fun z θ => (2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α)

/-- The projector coefficient `(Γ(θ)/c(α))·(2z²/(1+z)³)`, in the raw form. -/
def BcR (α : ℝ) : Fn :=
  fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)

/-- The nonlocal coefficient of `𝓛_Γ` is the separated one. -/
theorem Acoef_eq_AcR (α : ℝ) (z θ : ℝ) : Acoef α z θ = AcR α z θ := by
  rw [Acoef_eq_mul]
  rfl

/-- The projector coefficient of `𝕡` is the raw separated one. -/
theorem Bcoef_eq_BcR (α : ℝ) (z θ : ℝ) : Bcoef α z θ = BcR α z θ := rfl

/-- **`linPart` in the raw form of the three pieces.** -/
theorem linPart_eq_raw (α : ℝ) (f : Fn) :
    linPart α f
      = fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f := by
  rw [linPart_eq]
  funext z θ
  rw [Acoef_eq_AcR, show Bcoef α z θ = BcR α z θ from rfl]

/-! ## The projector piece -/

/-- **The projector piece.**  `BcR α · K0f f` is the constant `K0f f` times the fixed
`ℋ³`-function `BcR α`, so its level-three square is `(K0f f)² · HkSq α 3 (BcR α)`; with
`|K0f f| ≤ C₆|f|_{ℋ⁴}` and `|BcR α|_{ℋ³}² ≤ C₇` this is `C₆²C₇ |f|²_{ℋ⁴}`. -/
theorem proj_le (C6 C7 : ℝ) (h6 : 0 < C6) (h7 : 0 < C7)
    (hK0 : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → HkMem α 4 f →
      |K0f f| ≤ C6 * HkNorm α 4 f)
    (hB0 : ∀ (α : ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (BcR α) ∧ HkMem α 3 (BcR α) ∧
      HkSq α 3 (BcR α) ≤ C7) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => BcR α z θ * K0f f) ∧
      HkMem α 3 (fun z θ => BcR α z θ * K0f f) ∧
      HkSq α 3 (fun z θ => BcR α z θ * K0f f) ≤ C * HkSq α 4 f := by
  refine ⟨C6 ^ 2 * C7 + 1, by positivity, ?_⟩
  intro α f hα hα1 _hsm hmem4
  obtain ⟨hBsm, hBmem, hBsq⟩ := hB0 α hα hα1
  set c : ℝ := K0f f with hc
  have hK0b : |c| ≤ C6 * HkNorm α 4 f := hK0 α f hα hα1 hmem4
  have hfun : (fun z θ => BcR α z θ * K0f f) = fun z θ => c * BcR α z θ := by
    funext z θ; rw [hc]; ring
  rw [hfun]
  have hident : ∀ z θ, Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 3 (BcR α) z θ :=
    fun z θ => Work.FTS.GalBasis.hkIntegrand_const_mul α 3 c (BcR α) z θ
  have hmem : HkMem α 3 (fun z θ => c * BcR α z θ) := by
    constructor
    · intro z hz
      rw [show (fun θ => Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ)
          = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α 3 (BcR α) z θ from funext (hident z)]
      exact (hBmem.1 z hz).const_mul _
    · have hz : (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ)
          = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 3 (BcR α) z θ := by
        funext z
        rw [show (fun θ => Work.Spaces.HkIntegrand α 3 (fun z θ => c * BcR α z θ) z θ)
            = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α 3 (BcR α) z θ from
              funext (hident z), MeasureTheory.integral_const_mul]
      rw [hz]
      exact hBmem.2.const_mul _
  have hsq : HkSq α 3 (fun z θ => c * BcR α z θ) = c ^ 2 * HkSq α 3 (BcR α) := by
    rw [show (fun z θ => c * BcR α z θ) = c • BcR α from rfl,
      Work.FTS.EllipticEst.HkSq_smul]
  refine ⟨?_, hmem, ?_⟩
  · exact Work.FTS.EllipticEst.smoothOpen_const_mul' c hBsm
  · rw [hsq]
    have hc2 : c ^ 2 ≤ (C6 * HkNorm α 4 f) ^ 2 := by
      have h1 := abs_le.mp hK0b
      have h2 : (0:ℝ) ≤ C6 * HkNorm α 4 f :=
        mul_nonneg h6.le (Work.Spaces.HkNorm_nonneg α 4 f)
      nlinarith [h1.1, h1.2, h2]
    have hbig : c ^ 2 * HkSq α 3 (BcR α) ≤ (C6 * HkNorm α 4 f) ^ 2 * C7 :=
      mul_le_mul hc2 hBsq (Work.Spaces.HkSq_nonneg α 3 (BcR α))
        (sq_nonneg (C6 * HkNorm α 4 f))
    have hnorm_sq : HkNorm α 4 f ^ 2 = HkSq α 4 f := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    have htarget : (C6 * HkNorm α 4 f) ^ 2 * C7 = (C6 ^ 2 * C7) * HkSq α 4 f := by
      rw [mul_pow, hnorm_sq]; ring
    calc c ^ 2 * HkSq α 3 (BcR α) ≤ (C6 * HkNorm α 4 f) ^ 2 * C7 := hbig
      _ = (C6 ^ 2 * C7) * HkSq α 4 f := htarget
      _ ≤ (C6 ^ 2 * C7 + 1) * HkSq α 4 f := by
          have h0 : (0:ℝ) ≤ HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
          nlinarith [h0]

/-! ## The assembly -/

/-- **Assembly of the three pieces.**  Given the three piece estimates, the sum
`locOp f + AcR α · Mf f - BcR α · K0f f` is in `ℋ³` with a bound `C₃(1+|f|_{ℋ⁴})⁴`. -/
theorem assemble
    (C_loc C_A C_B : ℝ) (hCloc : 0 < C_loc) (hCA : 0 < C_A) (hCB : 0 < C_B)
    (hloc : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen (locOp f) ∧ HkMem α 3 (locOp f) ∧
      HkSq α 3 (locOp f) ≤ C_loc * HkSq α 4 f)
    (hA : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      HkMem α 4 f → Work.Construction.L12 f 0 = 0 →
      ContDiffOn ℝ 3 (Function.uncurry (fun z θ => AcR α z θ * Mf f z θ))
        Work.FTS.EllipticEst.Q0 ∧
      HkMem α 3 (fun z θ => AcR α z θ * Mf f z θ) ∧
      HkSq α 3 (fun z θ => AcR α z θ * Mf f z θ) ≤ C_A * HkSq α 4 f)
    (hB : ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => BcR α z θ * K0f f) ∧
      HkMem α 3 (fun z θ => BcR α z θ * K0f f) ∧
      HkSq α 3 (fun z θ => BcR α z θ * K0f f) ≤ C_B * HkSq α 4 f) :
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 6 f →
      Work.Construction.L12 f 0 = 0 →
      HkMem α 3 (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f) ∧
      HkNorm α 3 (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
        ≤ C3 * (1 + HkNorm α 4 f) ^ 4 := by
  refine ⟨Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) + 1, by
    have h1 : (0:ℝ) ≤ 4 * C_loc + 4 * C_A + 4 * C_B := by linarith
    have h2 := Real.sqrt_nonneg (4 * C_loc + 4 * C_A + 4 * C_B)
    linarith, ?_⟩
  intro α f hα hα1 hsm hmem6 h0
  have hmem4 : HkMem α 4 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem6
  obtain ⟨hLs, hLm, hLq⟩ := hloc α f hα hα1 hsm hmem4
  obtain ⟨hAsm, hAm, hAq⟩ := hA α f hα hα1 hsm hmem4 h0
  obtain ⟨hBs, hBm, hBq⟩ := hB α f hα hα1 hsm hmem4
  have hLsm : ContDiffOn ℝ 3 (Function.uncurry (locOp f)) Work.FTS.EllipticEst.Q0 :=
    hLs.forall 3
  have hBsm : ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => BcR α z θ * K0f f)) Work.FTS.EllipticEst.Q0 :=
    hBs.forall 3
  obtain ⟨hm3, hs3⟩ := Work.FTS.StrongPersist.L3Aux.HkMem_HkSq_add3_le α 3 (by norm_num)
    hLsm hAsm hBsm hLm hAm hBm
  have hSqnn : (0:ℝ) ≤ HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hbound : HkSq α 3
      (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
      ≤ (4 * C_loc + 4 * C_A + 4 * C_B) * HkSq α 4 f := by
    linarith [hs3, hLq, hAq, hBq, hSqnn]
  refine ⟨hm3, ?_⟩
  have hsqrt : HkNorm α 3
        (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
      ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * HkNorm α 4 f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    refine (Real.sqrt_le_sqrt hbound).trans_eq ?_
    rw [Real.sqrt_mul (by linarith : (0:ℝ) ≤ 4 * C_loc + 4 * C_A + 4 * C_B)]
  have hXn : HkNorm α 4 f ≤ (1 + HkNorm α 4 f) ^ 4 := by
    set x := HkNorm α 4 f with hx
    have hx0 : 0 ≤ x := Work.Spaces.HkNorm_nonneg α 4 f
    have h3 : (1:ℝ) ≤ (1 + x) ^ 3 := one_le_pow₀ (by linarith) (n := 3)
    have h4 : (1 + x) ≤ (1 + x) ^ 4 := by
      have : (1 + x) ^ 4 = (1 + x) * (1 + x) ^ 3 := by ring
      rw [this]
      exact le_mul_of_one_le_right (by linarith) h3
    linarith
  have hs : (0:ℝ) ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) := Real.sqrt_nonneg _
  have hX4 : (0:ℝ) ≤ (1 + HkNorm α 4 f) ^ 4 := by positivity
  calc HkNorm α 3
        (fun z θ => locOp f z θ + AcR α z θ * Mf f z θ - BcR α z θ * K0f f)
      ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * HkNorm α 4 f := hsqrt
    _ ≤ (Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) + 1)
          * (1 + HkNorm α 4 f) ^ 4 := by
        calc Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * HkNorm α 4 f
            ≤ Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) * (1 + HkNorm α 4 f) ^ 4 :=
              mul_le_mul_of_nonneg_left hXn hs
          _ ≤ (Real.sqrt (4 * C_loc + 4 * C_A + 4 * C_B) + 1)
                * (1 + HkNorm α 4 f) ^ 4 := by
              nlinarith [hs, hX4]

/-! ## The target -/

theorem L3_lin_mem : ∃ α₂ C3 : ℝ, 0 < α₂ ∧ 0 < C3 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongPersist.H6Adm α f →
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.linPart α f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.linPart α f)
        ≤ C3 * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 := by
  obtain ⟨C_loc, hCloc, hloc⟩ := Work.FTS.StrongPersist.L3Aux.locOp_HkSq_le
  obtain ⟨C_A, hCA, hA⟩ := Work.FTS.StrongPersist.L3Aux.Acoef_Mf_le
  obtain ⟨C6, hC6, hK0⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  obtain ⟨C7, hC7, hB0⟩ := Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le
  obtain ⟨C_B, hCB, hB⟩ := proj_le C6 C7 hC6 hC7 hK0 hB0
  obtain ⟨C3, hC3, hassemble⟩ := assemble C_loc C_A C_B hCloc hCA hCB hloc hA hB
  refine ⟨1, C3, one_pos, hC3, ?_⟩
  intro α hα f hf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : HkMem α 6 f := hf.reg.2
  have h0 : Work.Construction.L12 f 0 = 0 := hf.l12
  have hres := hassemble α f hα0 hα1 hsm hmem6 h0
  rw [linPart_eq_raw α f]
  refine ⟨hres.1, ?_⟩
  simpa only [Work.FTS.Nonlin.Xn] using hres.2

end Work.FTS.StrongPersist
