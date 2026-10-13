/-
Copyright: work module for the Elgindi finite-time singularity project.

# `bslOp α` commutes with `z²∂_z²` on the open quadrant

For data `Ψ` which are `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` and a source
`F = bslOp α Ψ` on `Q0`, the elliptic operator `bslOp α` of (PolarBSL) commutes with the
radial operator `Q := z²∂_z²`:

`bslOp α (z² ∂_z²Ψ) = z² ∂_z²F`   on `Q0`.

**Why it is true.**  On the open quadrant,
`bslOp α = -α²D_z² - 5αD_z + Lzero` with `D_z = z∂_z` (the identity `z²∂_z² = D_z² - D_z`
of `Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi`), and `Q = z²∂_z² = D_z² - D_z`
is itself a polynomial in `D_z`.  Now

* `Lzero` has `z`-independent coefficients, so it commutes with `D_z` (this is the content of
  `Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`, which proves
  `bslOp α (D_z^jΨ) = D_z^j(bslOp α Ψ)`);
* `D_z` commutes with every polynomial in `D_z`.

Hence `bslOp α` commutes with `Q`.  Formally the proof avoids the operator-algebra
bookkeeping altogether: `QΨ = D_z²Ψ - D_zΨ` pointwise on the open quadrant, so (by locality
of `bslOp` on the open quadrant) the left-hand side is
`bslOp α (D_z²Ψ - D_zΨ)`, and by linearity of `bslOp` this is
`bslOp α (D_z²Ψ) - bslOp α (D_zΨ) = D_z²F - D_zF` (the radially differentiated equation),
which is `z²∂_z²F` since `F`, being `bslOp α Ψ` on the open quadrant, is `C^∞` there.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.H2W.z2pzIter2Comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Linearity of the individual derivatives in `bslOp` for a subtraction

The counterparts of `Work.Elliptic.pz_add`, `Work.Elliptic.pzIter_two_add`,
`Work.Elliptic.pthIter_two_add`, `Work.Elliptic.pth_tan_mul_add`, `Work.Elliptic.Lzero_add`
and `Work.Elliptic.bslOp_add` (in `Submission.Work.Elliptic.bslOp_add`) for `f - g`.  The
differentiability hypotheses are genuinely needed: `deriv` is totalised, so e.g.
`deriv (f - g) = deriv f - deriv g` requires differentiability of both summands. -/

/-- `∂_z` is additive for a subtraction on `C²` functions. -/
theorem pz_sub_Q0 (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pz (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pz f z θ - Work.Spaces.pz g z θ := by
  rw [Work.Elliptic.pz_eq_iteratedDeriv_one (fun z θ => f z θ - g z θ) z θ,
    Work.Elliptic.pz_eq_iteratedDeriv_one f z θ,
    Work.Elliptic.pz_eq_iteratedDeriv_one g z θ]
  exact iteratedDeriv_sub
    (Work.Elliptic.contDiffAt_uncurry_slice_fst f z θ (hf.of_le (m := 1) (by norm_num)))
    (Work.Elliptic.contDiffAt_uncurry_slice_fst g z θ (hg.of_le (m := 1) (by norm_num)))

/-- `∂_zz` is additive for a subtraction on `C²` functions. -/
theorem pzIter_two_sub_Q0 (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pzIter 2 (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pzIter 2 f z θ - Work.Spaces.pzIter 2 g z θ := by
  rw [Work.Elliptic.pzIter_eq_iteratedDeriv 2 (fun z θ => f z θ - g z θ) z θ,
    Work.Elliptic.pzIter_eq_iteratedDeriv 2 f z θ,
    Work.Elliptic.pzIter_eq_iteratedDeriv 2 g z θ]
  exact iteratedDeriv_sub (Work.Elliptic.contDiffAt_uncurry_slice_fst f z θ hf)
    (Work.Elliptic.contDiffAt_uncurry_slice_fst g z θ hg)

/-- `∂_θθ` is additive for a subtraction on `C²` functions. -/
theorem pthIter_two_sub_Q0 (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pthIter 2 (fun z θ => f z θ - g z θ) z θ
      = Work.Spaces.pthIter 2 f z θ - Work.Spaces.pthIter 2 g z θ := by
  rw [Work.Elliptic.pthIter_eq_iteratedDeriv 2 (fun z θ => f z θ - g z θ) z θ,
    Work.Elliptic.pthIter_eq_iteratedDeriv 2 f z θ,
    Work.Elliptic.pthIter_eq_iteratedDeriv 2 g z θ]
  exact iteratedDeriv_sub (Work.Elliptic.contDiffAt_uncurry_slice_snd f z θ hf)
    (Work.Elliptic.contDiffAt_uncurry_slice_snd g z θ hg)

/-- `∂_θ(tan θ · ·)` is additive for a subtraction on `C²` functions (at `θ` with
`cos θ ≠ 0`). -/
theorem pth_tan_mul_sub_Q0 (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pth (fun z θ => Real.tan θ * (f z θ - g z θ)) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
        - Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ := by
  have h1 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * f z θ') θ :=
    ((Real.contDiffAt_tan.mpr hθ).mul
      (Work.Elliptic.contDiffAt_uncurry_slice_snd f z θ
        (hf.of_le (m := 1) (by norm_num)))).differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fun θ' => Real.tan θ' * g z θ') θ :=
    ((Real.contDiffAt_tan.mpr hθ).mul
      (Work.Elliptic.contDiffAt_uncurry_slice_snd g z θ
        (hg.of_le (m := 1) (by norm_num)))).differentiableAt (by norm_num)
  simp only [Work.Spaces.pth]
  have key : (fun θ' : ℝ => Real.tan θ' * (f z θ' - g z θ'))
      = (fun θ' : ℝ => Real.tan θ' * f z θ' - Real.tan θ' * g z θ') := by
    funext θ'; ring
  rw [key]
  exact deriv_sub h1 h2

/-- `Lzero` is additive for a subtraction of `C²` functions. -/
theorem Lzero_sub_Q0 (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Elliptic.Lzero (fun z θ => f z θ - g z θ) z θ
      = Work.Elliptic.Lzero f z θ - Work.Elliptic.Lzero g z θ := by
  have h2 := pthIter_two_sub_Q0 f g z θ hf hg
  have ht := pth_tan_mul_sub_Q0 f g z θ hθ hf hg
  simp only [Work.Elliptic.Lzero, h2, ht]
  ring

/-- `bslOp α` is additive for a subtraction of `C²` functions. -/
theorem bslOp_sub_Q0 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ => f z θ - g z θ) z θ
      = Work.Elliptic.bslOp α f z θ - Work.Elliptic.bslOp α g z θ := by
  have h2 := pzIter_two_sub_Q0 f g z θ hf hg
  have h1 := pz_sub_Q0 f g z θ hf hg
  have hL := Lzero_sub_Q0 f g z θ hθ hf hg
  simp only [Work.Elliptic.bslOp_apply, h2, h1, hL]
  ring

/-! ## Locality of `bslOp α` on the open quadrant -/

/-- **`bslOp α` depends only on a neighbourhood.**  Two functions agreeing on the open quadrant
have the same `bslOp α` there.  (All the ingredients of `bslOp` — `∂_z`, `∂_zz`, `∂_θθ` and
`∂_θ(tan θ ·)` — are local; only the congruence of the plain partial derivatives
`Work.Spaces.pz_congr_of_isOpen` / `Work.Spaces.pth_congr_of_isOpen` is needed, iterated once
for the second order operators.) -/
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

/-! ## The commutation `bslOp α (z²∂_z²Ψ) = z²∂_z²(bslOp α Ψ)` -/

/-- **The elliptic operator `bslOp α` commutes with the radial operator `z²∂_z²`** on the open
quadrant: if `bslOp α Ψ = F` there and `Ψ` is `C^∞` there, then `bslOp α (z²∂_z²Ψ) = z²∂_z²F`
there.  This is the `j = 2` mixed-radial instance of the paper's "the equation commutes with
`D_R` derivatives" (§H2, tex 950), in the form in which the radial part of the `ℋ²`-norm of
`z²∂_zzΨ` is estimated. -/
theorem bslOp_zsq_pzIter2 (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
  intro z hz θ hθ0 hθ1
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hG : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ : 0 < Real.cos θ)
  have hFG : ∀ a b, 0 < a → 0 < b → b < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ a b = F a b := fun a b ha hb0 hb1 => heq a ha b hb0 hb1
  have hCd2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter 2 Ψ)) (z, θ) :=
    ((hΨ.DzIter 2).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  have hCd1 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 Ψ)) (z, θ) :=
    ((hΨ.DzIter 1).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  -- (1) `z²∂_z²Ψ = D_z²Ψ - D_zΨ` on the open quadrant, and `bslOp α` is local there
  have hL : Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Elliptic.bslOp α
          (fun z θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) z θ :=
    bslOp_congr_Q0 α (fun a b ha hb0 hb1 =>
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ ha ⟨hb0, hb1⟩) z θ hz hθ0 hθ1
  -- (2) linearity of `bslOp α` with respect to the subtraction
  have hSub := bslOp_sub_Q0 α (Work.Spaces.DzIter 2 Ψ) (Work.Spaces.DzIter 1 Ψ) z θ hcos hCd2 hCd1
  -- (3) the radially differentiated elliptic equations for `j = 1, 2`
  have hE2 := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 2 hsm heq z hz θ hθ0 hθ1
  have hE1 := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 hsm heq z hz θ hθ0 hθ1
  -- (4) `F` agrees with `bslOp α Ψ` on the open quadrant, so it is smooth there
  have hR1 : z ^ 2 * Work.Spaces.pzIter 2 F z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ := by
    congr 1
    refine Work.Elliptic.pzIter_congr_nhds 2 ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with a ha
    exact (hFG a θ ha hθ0 hθ1).symm
  have hR2 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Elliptic.bslOp α Ψ) z θ :=
    Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Elliptic.bslOp α Ψ) hG hz hθI
  have hR3 : Work.Spaces.DzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
    have e2 : Work.Spaces.DzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        = Work.Spaces.DzIter 2 F z θ :=
      Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ) (G := F)
        hFG 2 z θ hz hθ0 hθ1
    have e1 : Work.Spaces.DzIter 1 (Work.Elliptic.bslOp α Ψ) z θ
        = Work.Spaces.DzIter 1 F z θ :=
      Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ) (G := F)
        hFG 1 z θ hz hθ0 hθ1
    rw [e2, e1]
  have hR4 : Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
      = Work.Elliptic.bslOp α (Work.Spaces.DzIter 2 Ψ) z θ
        - Work.Elliptic.bslOp α (Work.Spaces.DzIter 1 Ψ) z θ := by
    rw [← hE2, ← hE1]
  calc Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Elliptic.bslOp α
          (fun z θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) z θ := hL
    _ = Work.Elliptic.bslOp α (Work.Spaces.DzIter 2 Ψ) z θ
          - Work.Elliptic.bslOp α (Work.Spaces.DzIter 1 Ψ) z θ := hSub
    _ = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by rw [hE2, hE1]
    _ = Work.Spaces.DzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
          - Work.Spaces.DzIter 1 (Work.Elliptic.bslOp α Ψ) z θ := hR3.symm
    _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ := hR2.symm
    _ = z ^ 2 * Work.Spaces.pzIter 2 F z θ := hR1.symm

end Work.FTS.EllipticEst.H2W
