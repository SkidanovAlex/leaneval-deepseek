/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular-moment equation of the slice `z²∂_z²Ψ`

This module proves `Work.H2W.asliceMomentEq`:

for a datum `h : TT.EllWeakPos α 2 F Ψ` of the weak hypothesis class and every `z > 0`,

  `∫_θ (Lzero1 (z²∂_z²Ψ(z,·)) θ) · sinθcos²θ dθ = F_*(D_z²F)(z) + α² F_*(D_z⁴Ψ)(z)`,

where `F_*(f)(z) = ∫_θ f(z,θ) sinθcos²θ dθ` and `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`.

## The route

Write `A := z²∂_z²Ψ`.  On the open quadrant `A = D_z²Ψ - D_zΨ` and `bslOp α` commutes with
`z²∂_z²` (`H2W.bslOp_zsq_pzIter2`), so

  `bslOp α A = z²∂_z²F = D_z²F - D_zF`.

Combining this with `Lzero A = bslOp α A + α²D_z²A + 5αD_zA` (`bslOp_apply` plus
`z²∂_z² = D_z² - D_z` and `z∂_z = D_z`) gives the pointwise identity

  `Lzero A = (D_z²F - D_zF) + α²D_z²A + 5αD_zA`

on the open quadrant (`lzero1_zsq_pzIter2_eq`), and it is co-null in `θ` (`ae_Ioo_mem`).
Each of the four summands is `θ`-integrable against `sinθcos²θ`: they are the `D_z`-slots
(`i ≤ 2`) of the `ℋ²`-memberships `HkMem α 2 F` and `HkMem α 2 A`, by the elementary
domination `|g·sinθcos²θ| ≤ (g·w/sin(2θ)^{η/2})² + 1 ≤ HkIntegrand + 1`
(`integrableOn_DzIter_mul_sinCos2`).  Integrating termwise therefore gives

  `∫ Lzero1 (A-slice) · sinθcos²θ
      = F_*(D_z²F) - F_*(D_zF) + α²F_*(D_z²A) + 5αF_*(D_zA)`.

Finally the moment chain identifies each term: `F_*(D_zF) = 0`
(`remov.Fstar_DzIter_one_F_ge_two`, needing `k ≥ 2`), `F_*(D_z^jΨ) = 0` for `j ≤ 3`
pointwise (`H2W.MomentAe.Fstar_DzIter_le_Psi`), and — via the a.e. identities
`D_zA = D_z³Ψ - D_z²Ψ`, `D_z²A = D_z⁴Ψ - D_z³Ψ` of `H2W.MomentAe.DzIter_zsq_pzIter2_eq` —
`F_*(D_zA) = F_*(D_z³Ψ) - F_*(D_z²Ψ) = 0` and
`F_*(D_z²A) = F_*(D_z⁴Ψ) - F_*(D_z³Ψ) = F_*(D_z⁴Ψ)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.H2W.momentChainAe
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq
import Submission.Work.FTS.EllipticEst.remov.SourceBound.aesm_F_slots
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Honesty of a `D_z`-slot against the angular profile -/

/-- **A `D_z`-slot of an `ℋ^k`-function is integrable against `sinθcos²θ`.**

For `g` of class `C^∞` on the open quadrant with `Work.Spaces.HkMem α k g` one has, for every
`i ≤ k` and every `z > 0`, the `θ`-integrability

  `∫_θ |D_z^i g(z,θ) · sinθcos²θ| < ∞`.

The proof is the pointwise domination `|g·sinθcos²θ| ≤ (g·w(z)/sin(2θ)^{η/2})² + 1`, whose
first summand is a single summand of the `ℋ^k`-integrand `HkIntegrand` (`sq_le_HkIntegrand_z`
and `abs_mul_sinCos2_le_weighted`), together with the a.e. strong measurability of the slice
(continuity of `D_z^i g` on the open quadrant). -/
theorem integrableOn_DzIter_mul_sinCos2 {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter i g z θ * sg θ) Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hvol : MeasureTheory.volume Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hsin : Continuous (fun p : ℝ × ℝ => sg p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  refine MeasureTheory.Integrable.mono'
    ((hm.1 z hzI).add (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol))
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2 * sg p.2)
      ((hsm.DzIter i).continuousOn.mul hsin.continuousOn) hz) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs]
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.DzIter i g z θ) hz hθ
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi
  simp only [Pi.add_apply]
  linarith

/-! ## The pointwise differentiated-equation identity -/

/-- **The elliptic equation, twice radially differentiated, read on the slice `z²∂_z²Ψ`.**

On the open quadrant,
`Lzero1 (z²∂_z²Ψ(z,·)) = (D_z²F - D_zF) + α²D_z²(z²∂_z²Ψ) + 5αD_z(z²∂_z²Ψ)`.

The identity is the combination of `H2W.bslOp_zsq_pzIter2` (`bslOp α (z²∂_z²Ψ) = z²∂_z²F`,
i.e. `= D_z²F - D_zF`) with the elementary relations `z²∂_z² = D_z² - D_z` and
`z∂_z = D_z`. -/
theorem lzero1_zsq_pzIter2_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hFs : Work.FTS.EllipticEst.SmoothOpen F)
    (hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        + α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + 5 * α * Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨs
  have hbsl : Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
    rw [Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2 α F Ψ heq hsm z hz θ hθ0 hθ1,
      Work.H2W.MomentAe.zsq_pzIter2_eq hFs hz hθI]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hdec : Work.Elliptic.Lzero (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
        + α * (5 + α) * z * Work.Spaces.pz
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    rw [Work.Elliptic.bslOp_apply]; ring
  have hAA : z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    Work.H2W.MomentAe.zsq_pzIter2_eq hA hz hθI
  have hstep : Work.FTS.EllipticEst.Lzero1
      (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = Work.Elliptic.Lzero (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := rfl
  rw [hstep, hdec, hbsl, hAA]
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  ring

/-! ## The moment identities of the two `A`-slots -/

/-- `F_*(D_zA) = 0` on the open quadrant: the a.e. identity `D_zA = D_z³Ψ - D_z²Ψ` turns the
moment of `D_zA` into the difference of the two vanishing moments of `D_z³Ψ` and `D_z²Ψ`. -/
theorem fstar_zsq_Dz_eq_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 := by
  have hmom3 : Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z = 0 :=
    Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 3 (by norm_num) z hz
  have hmom2 : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0 :=
    Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 2 (by norm_num) z hz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ) Iθ :=
    (Work.H2W.MomentAe.level_bound hΨs h.memA h.memB 3 (by norm_num)).1 z hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 Ψ z θ * sg θ) Iθ :=
    (Work.H2W.MomentAe.level_bound hΨs h.memA h.memB 2 (by norm_num)).1 z hz
  have hae : (fun θ => Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ
        - Work.Spaces.DzIter 2 Ψ z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨs 1 hz hθ]
    ring
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      = ∫ θ in Iθ, Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := rfl
    _ = ∫ θ in Iθ, (Work.Spaces.DzIter 3 Ψ z θ * sg θ
          - Work.Spaces.DzIter 2 Ψ z θ * sg θ) := MeasureTheory.integral_congr_ae hae
    _ = (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * sg θ)
          - (∫ θ in Iθ, Work.Spaces.DzIter 2 Ψ z θ * sg θ) :=
        MeasureTheory.integral_sub h3 h2
    _ = Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z
          - Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z := rfl
    _ = 0 := by rw [hmom3, hmom2, sub_self]

/-- `F_*(D_z²A) = F_*(D_z⁴Ψ)` on the open quadrant: the a.e. identity
`D_z²A = D_z⁴Ψ - D_z³Ψ` together with the vanishing of `F_*(D_z³Ψ)`. -/
theorem fstar_DzIter_two_zsq_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z := by
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 (Work.H2W.MomentAe.smoothOpen_zsq hΨs) h.memA 2 le_rfl hz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ) Iθ :=
    (Work.H2W.MomentAe.level_bound hΨs h.memA h.memB 3 (by norm_num)).1 z hz
  have h4 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 4 Ψ z θ * sg θ) Iθ := by
    have hae : (fun θ => Work.Spaces.DzIter 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ
          + Work.Spaces.DzIter 3 Ψ z θ * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => Work.Spaces.DzIter 4 Ψ z θ * sg θ) := by
      filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
      rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨs 2 hz hθ]
      ring
    exact (hA2.add h3).congr hae
  have hmom3 : Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z = 0 :=
    Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 3 (by norm_num) z hz
  have hae2 : (fun θ => Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 4 Ψ z θ * sg θ
        - Work.Spaces.DzIter 3 Ψ z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨs 2 hz hθ]
    ring
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      = ∫ θ in Iθ, Work.Spaces.DzIter 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ := rfl
    _ = ∫ θ in Iθ, (Work.Spaces.DzIter 4 Ψ z θ * sg θ
          - Work.Spaces.DzIter 3 Ψ z θ * sg θ) := MeasureTheory.integral_congr_ae hae2
    _ = (∫ θ in Iθ, Work.Spaces.DzIter 4 Ψ z θ * sg θ)
          - (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * sg θ) :=
        MeasureTheory.integral_sub h4 h3
    _ = Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z
          - Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z := rfl
    _ = Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z := by rw [hmom3, sub_zero]

/-! ## The target -/

theorem asliceMomentEq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
          + α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z := by
  intro z hz
  have hΨs : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨hFs, -, hAs, -⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  -- the four honest slots
  have hF1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 F z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hFs h.memF 1 (by norm_num) hz
  have hF2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hFs h.memF 2 le_rfl hz
  have hA1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hAs h.memA 1 (by norm_num) hz
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ) Iθ :=
    integrableOn_DzIter_mul_sinCos2 hAs h.memA 2 le_rfl hz
  -- the integrand identity on the open interval, and the termwise integration
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * sg θ
        = ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
            + α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + 5 * α * Work.Spaces.DzIter 1
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ := by
    intro θ hθ
    rw [lzero1_zsq_pzIter2_eq h.eq h.smooth hFs hΨs hz hθ.1 hθ.2]
  have hsplit : (fun θ => ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
        + α ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + 5 * α * Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      = (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ)
        - (fun θ => Work.Spaces.DzIter 1 F z θ * sg θ)
        + (fun θ => α ^ 2 * (Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ))
        + (fun θ => 5 * α * (Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)) := by
    funext θ
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hid : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1
        (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * sg θ)
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z
        + α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
        + 5 * α * Work.Elliptic.Fstar (Work.Spaces.DzIter 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z := by
    have hae : (fun θ => Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
            + α ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + 5 * α * Work.Spaces.DzIter 1
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt
    have hsplit : (fun θ => ((Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
          + α ^ 2 * Work.Spaces.DzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + 5 * α * Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ
          - Work.Spaces.DzIter 1 F z θ * sg θ
          + α ^ 2 * (Work.Spaces.DzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
          + 5 * α * (Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)) := by
      filter_upwards with θ
      ring
    rw [MeasureTheory.integral_congr_ae (hae.trans hsplit)]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_add]
      · rw [MeasureTheory.integral_sub]
        · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
        · exact hF2
        · exact hF1
      · exact hF2.sub hF1
      · exact hA2.const_mul (α ^ 2)
    · exact (hF2.sub hF1).add (hA2.const_mul (α ^ 2))
    · exact hA1.const_mul (5 * α)
  -- the moment values
  have hF1zero : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 :=
    Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two le_rfl h z hz
  have hA1zero := fstar_zsq_Dz_eq_zero h hΨs hz
  have hA2eq := fstar_DzIter_two_zsq_eq h hΨs hz
  rw [hid, hF1zero, hA1zero, hA2eq]
  ring

end Work.H2W
