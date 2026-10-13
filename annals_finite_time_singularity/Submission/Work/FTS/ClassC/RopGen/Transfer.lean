/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.RopGen.Transfer` — the `ℛ`-transfer at *general solution level* `K`

This is the level-parametric form of `Work.FTS.ClassC.ropTransferCore_of_pieces`
(`Submission/Work/FTS/ClassC/ropTransferCore_classC.lean`): the `ℛ`-component of the elliptic
package of the design (item A4) at level `k`, over the *solution class* `EllClassOk K` with
`k + 2 ≤ K` (the sharp level: the level-`k` slot needs the honesty of the quotient
`Ξ/sin 2θ` at level `k+1`, hence the angular traces of `D_z^j Ξ` for `j ≤ k+1 ≤ K-1`,
`dzIterTracesOfLevel.dzIter_traces_of_level`).

The analytic content is isolated in two *pieces*, exactly as in the level-`7` development
(`RopCoreHkMem`, `RopCoreNorm`), now at general class level:

* `hHon : RopHon k K` — the honesty of the quotient `Ξ/sin 2θ`, of the smoothed profile
  `sin²θ·(α D_z(Ξ/sin 2θ))` and of `∂_θΞ`
  (sibling `Work.FTS.ClassC.ropHkMemPiecesGen`);
* `hNor : RopNor k K` — the four norm pieces: the two divisions by `sin 2θ`, the angular
  Poincaré estimate and the `α D_z` estimate
  (siblings `Work.FTS.ClassC.ropNormPiecesGen`, `Work.FTS.ClassC.ropAlphaDzGen`).

The assembly below is the *pointwise identity of the paper* on the open quadrant

  `ℛ(Ξ) = 4 sin²θ·Φ + 2 α sin²θ·D_zΦ + ∂_θΞ`,    `Φ = Ξ/sin 2θ`, `Ξ = PhiTil α g Ψ`,

together with the `sin²θ`-multiplier estimate `Blocks.HkMul_ang_le`, the honesty transfers
(`HkMem_add_open`, `HkMem_agreeOnQ`, `HkMem_const_mul`) and the triangle inequalities
(`HkNorm_add_le`, `HkNorm_const_mul`) — i.e. precisely the constants of
`ropTransferCore_of_pieces`, with `7 ↦ K` and `EllClassOk 7 ↦ EllClassOk K`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.ropBasic
import Submission.Work.FTS.EllSol.ropIdentity
import Submission.Work.FTS.EllSol.PkgK5.VopcPth2TransferGen
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The definitional identification with the residual -/

/-- `Construction.PhiTil α g Ψ = Elliptic.EllResid α g Ψ` (definitional). -/
theorem phiTil_eq_EllResid_gen (α : ℝ) (g Ψ : Fn) :
    Work.Construction.PhiTil α g Ψ = Work.Elliptic.EllResid α g Ψ := by
  funext z θ
  simp only [Work.Construction.PhiTil, Work.Elliptic.EllResid, Work.Construction.Theta,
    Work.Construction.s2_eq]
  rw [show Work.Elliptic.L12 g z = Work.Construction.L12 g z from rfl]

/-! ## Smoothness on the open quadrant, at general solution level -/

/-- `Ḡ(α,g)·sin 2θ` is `C^∞` on the open quadrant for every `g` of the class `C`
(the level-parametric form of `smoothOpen_GbarSin_classC`, whose `7` was incidental). -/
theorem smoothOpen_GbarSin_gen' {α : ℝ} (hα : 0 < α) {g : Fn} (hg : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
  Work.FTS.EllSol.PkgK5.smoothOpen_GbarSin_gen hα 7 hg.reg hg.fsm hg.mem

/-- **The residual `PhiTil α g Ψ` is `C^∞` on the open quadrant** at *any* solution level
(the level-`K` form of `smoothOpen_phiTil`; only `ClassC α g` and the open-quadrant smoothness
carried by `EllClassOk K` are used). -/
theorem smoothOpen_phiTil_gen {α : ℝ} {K : ℕ} {g Ψ : Fn} (hα : 0 < α) (hg : ClassC α g)
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ) := by
  have hSmW : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllExist.shiftSing α g Ψ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.EllipticEst.TT.EllWeakPos.smooth h.2.2)
  have hGnegSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) := by
    have hL := smoothOpen_GbarSin_gen' hα hg
    refine Work.FTS.EllipticEst.SmoothOpen.congr (hL.const_mul' (-1)) ?_
    intro z' θ' _ _ _
    ring
  have hdecomp : Work.Construction.PhiTil α g Ψ
      = fun z' θ' => Work.FTS.EllExist.shiftSing α g Ψ z' θ'
          + (-(Work.Elliptic.Gbar α g z')) * Real.sin (2 * θ') := by
    funext z' θ'
    rw [phiTil_eq_EllResid_gen]
    simp only [Work.Elliptic.EllResid, Work.FTS.EllExist.shiftSing_apply, Work.Elliptic.Gsing,
      Work.Elliptic.Gstar]
    ring
  refine Work.FTS.EllipticEst.SmoothOpen.congr
    (Work.FTS.EllipticEst.SmoothOpen.add hSmW hGnegSm) ?_
  intro z' θ' _ _ _
  exact (congrFun (congrFun hdecomp z') θ').symm

/-- The quotient `PhiTil α g Ψ / sin 2θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_div_sin_gen {α : ℝ} {K : ℕ} {g Ψ : Fn} (hα : 0 < α) (hg : ClassC α g)
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.PhiTil α g Ψ z θ / Real.sin (2 * θ)) :=
  Work.FTS.EllSol.smoothOpen_div_sin_local (smoothOpen_phiTil_gen hα hg h)

/-- **The `ℛ`-output `ℛ(PhiTil α g Ψ)` is `C^∞` on the open quadrant** at any solution level. -/
theorem smoothOpen_rop_phiTil_gen {α : ℝ} {K : ℕ} {g Ψ : Fn} (hα : 0 < α) (hg : ClassC α g)
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ)) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.EllipticEst.Rop α (Work.Elliptic.EllResid α g Ψ)) :=
    Work.FTS.EllSol.smoothOpen_Rop_local (smoothOpen_phiTil_gen hα hg h)
  refine Work.FTS.EllipticEst.SmoothOpen.congr h1 ?_
  intro z θ _ _ _
  rw [phiTil_eq_EllResid_gen]
  rfl

/-- A sum of two functions `C^∞` on the open quadrant is `C^∞` there. -/
theorem smoothOpen_add_local_gen {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h := (hf.forall n).add (hg.forall n)
  rw [show Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g from rfl]
  exact h

/-- **The structural identity of the `ℛ`-core on the open quadrant** at general solution level:
`ℛ(Ξ) = 4 sin²θ·Φ + 2 α sin²θ·D_zΦ + ∂_θΞ` with `Φ = Ξ/sin 2θ`, `Ξ = PhiTil α g Ψ`. -/
theorem rop_phiTil_eq_sin_sq_gen {α : ℝ} {K : ℕ} {g Ψ : Fn} (hα : 0 < α) (hg : ClassC α g)
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ) z θ
      = 4 * Real.sin θ ^ 2
          * (Work.Construction.PhiTil α g Ψ z θ / Real.sin (2 * θ))
        + 2 * Real.sin θ ^ 2 * (α * Work.Spaces.Dz
            (fun z θ => Work.Construction.PhiTil α g Ψ z θ / Real.sin (2 * θ)) z θ)
        + Work.Spaces.pth (Work.Construction.PhiTil α g Ψ) z θ := by
  have hSΦ := smoothOpen_div_sin_gen hα hg h
  have hd : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Ψ z θ' / Real.sin (2 * θ')) θ :=
    ((hSΦ.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)).differentiableAt
      (by simp [Work.Stability.smoothOrder])
  have h1 := Work.FTS.EllSol.Rop_EllResid_eq_sin_sq_local α g Ψ hz hθ0 hθ1 hd
  simp only [← phiTil_eq_EllResid_gen] at h1 ⊢
  exact h1

/-! ## The two pieces of the transfer, and the transfer itself -/

/-- **The honesty pieces of the `ℛ`-core at general class level**: the honesty of the quotient
`Ξ/sin 2θ`, of the smoothed profile `sin²θ·(α D_z(Ξ/sin 2θ))` and of `∂_θΞ`
(`Ξ = PhiTil α g Ψ`).  (The level-parametric form of `RopCoreHkMem`.) -/
def RopHon (k K : ℕ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk K α g Ψ →
    Work.Spaces.HkMem α k
        (fun z θ => Work.Construction.PhiTil α g Ψ z θ / Real.sin (2 * θ)) ∧
    Work.Spaces.HkMem α k (fun z θ => Real.sin θ ^ 2 *
        (α * Work.Spaces.Dz (fun z θ => Work.Construction.PhiTil α g Ψ z θ
          / Real.sin (2 * θ)) z θ)) ∧
    Work.Spaces.HkMem α k (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ))

/-- **The four norm pieces of the `ℛ`-core at general class level** (the level-parametric form of
`RopCoreNorm`): the two divisions by `sin 2θ`, the angular Poincaré estimate, and the `α D_z`
estimate. -/
def RopNor (k K : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk K α g Ψ →
    Work.Spaces.HkNorm α k
        (fun z θ => Work.Construction.PhiTil α g Ψ z θ / Real.sin (2 * θ))
      ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ)) ∧
    Work.Spaces.HkNorm α k (fun z θ => Real.sin θ ^ 2 *
        (α * Work.Spaces.Dz (fun z θ => Work.Construction.PhiTil α g Ψ z θ
          / Real.sin (2 * θ)) z θ))
      ≤ C * α * Work.Spaces.HkNorm α k
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ))) ∧
    Work.Spaces.HkNorm α k (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ))
      ≤ C * Work.Spaces.HkNorm α k
          (Work.Spaces.pthIter 2 (Work.Construction.PhiTil α g Ψ)) ∧
    α * Work.Spaces.HkNorm α k
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ)))
      ≤ C * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.Construction.PhiTil α g Ψ))
          + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α k g)

/-- **The `ℛ`-transfer at level `k` over the solution class `EllClassOk K`**, from the two
pieces: the honesty of `ℛ(Ξ)` together with the a-priori bound

  `|ℛ(Ξ)|_{ℋᵏ} ≤ C (|∂_θθΞ|_{ℋᵏ} + α²|z²∂_z²Ψ|_{ℋᵏ} + |g|_{ℋᵏ})`,   `Ξ = PhiTil α g Ψ`,

whose two elliptic terms are exactly the left-hand side of `RemovingL12KLe`.  This is
`ropTransferCore_of_pieces` with `EllClassOk 7 ↦ EllClassOk K`. -/
theorem ropTransfer_of_pieces (k K : ℕ) (hHon : RopHon k K) (hNor : RopNor k K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
      Work.FTS.EllExist.EllClassOk K α g Ψ →
      Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
        ≤ C * (Work.Spaces.HkNorm α k
              (Work.Spaces.pthIter 2 (Work.Construction.PhiTil α g Ψ))
            + α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α k g) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.Blocks.HkMul_ang_le k
  obtain ⟨Cn, hCnpos, hCn⟩ := hNor
  refine ⟨2 * (4 * Real.sqrt Cm * Cn * Cn + 2 * Cn * Cn + Cn), by positivity, ?_⟩
  intro α g Ψ hα hα4 hg hO
  have hα1 : α ≤ 1 := by linarith
  have hCm0 : 0 ≤ Cm := le_of_lt hCmpos
  have hCn0 : 0 ≤ Cn := le_of_lt hCnpos
  obtain ⟨hmΦ, hmA', hmPth⟩ := hHon α g Ψ hα hα4 hg hO
  obtain ⟨hN1, hN2, hN3, hN4⟩ := hCn α g Ψ hα hα4 hg hO
  have hSmΞ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ) :=
    smoothOpen_phiTil_gen hα hg hO
  set Φ : ℝ → ℝ → ℝ := fun z θ => Work.Construction.PhiTil α g Ψ z θ / Real.sin (2 * θ)
    with hΦdef
  have hSmΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllSol.smoothOpen_div_sin_local hSmΞ
  set A : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * Φ z θ with hAdef
  set A' : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * (α * Work.Spaces.Dz Φ z θ) with hA'def
  set Cc : ℝ → ℝ → ℝ := Work.Spaces.pth (Work.Construction.PhiTil α g Ψ) with hCdef
  have hSmA : Work.FTS.EllipticEst.SmoothOpen A :=
    Work.FTS.EllSol.SmoothOpen_mul_sin_sq_local hSmΦ
  have hSmA' : Work.FTS.EllipticEst.SmoothOpen A' :=
    Work.FTS.EllSol.SmoothOpen_mul_sin_sq_local (hSmΦ.Dz.const_mul' α)
  have hSmC : Work.FTS.EllipticEst.SmoothOpen Cc := hSmΞ.pth
  have hmA : Work.Spaces.HkMem α k A := ((hCm α Φ hα hα1 hSmΦ).2.2 hmΦ).2.2.1
  -- #### the aggregated function and its honesty
  have hSm4A : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (4 : ℝ) * A z θ) :=
    hSmA.const_mul' 4
  have hSm2A' : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (2 : ℝ) * A' z θ) :=
    hSmA'.const_mul' 2
  have hSm2A'C : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (2 : ℝ) * A' z θ + Cc z θ) :=
    smoothOpen_add_local_gen hSm2A' hSmC
  have hm4A : Work.Spaces.HkMem α k (fun z θ => (4 : ℝ) * A z θ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hSm4A
      (fun z θ _ _ _ => by simp [Pi.smul_apply, smul_eq_mul])
      (Work.FTS.EllipticEst.HkMem_smul (c := (4 : ℝ)) (by norm_num) α k hmA)
  have hm2A' : Work.Spaces.HkMem α k (fun z θ => (2 : ℝ) * A' z θ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hSm2A'
      (fun z θ _ _ _ => by simp [Pi.smul_apply, smul_eq_mul])
      (Work.FTS.EllipticEst.HkMem_smul (c := (2 : ℝ)) (by norm_num) α k hmA')
  have hm2A'C : Work.Spaces.HkMem α k (fun z θ => (2 : ℝ) * A' z θ + Cc z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hSm2A' hSmC hm2A' hmPth
  have hmG : Work.Spaces.HkMem α k
      (fun z θ => (4 : ℝ) * A z θ + ((2 : ℝ) * A' z θ + Cc z θ)) :=
    Work.FTS.EllipticEst.HkMem_add_open hSm4A hSm2A'C hm4A hm2A'C
  -- #### the pointwise identity
  have hAgree : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => (4 : ℝ) * A z θ + ((2 : ℝ) * A' z θ + Cc z θ))
      (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ)) := by
    intro z θ hz hθ0 hθ1
    have h1 := rop_phiTil_eq_sin_sq_gen (α := α) (K := K) (g := g) (Ψ := Ψ) hα hg hO hz hθ0 hθ1
    simp only [hAdef, hA'def, hCdef, hΦdef]
    rw [h1]
    ring
  have hmRop : Work.Spaces.HkMem α k
      (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ)) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ (smoothOpen_rop_phiTil_gen hα hg hO) hAgree hmG
  -- #### the estimate
  set X : ℝ := Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Construction.PhiTil α g Ψ))
    + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    + Work.Spaces.HkNorm α k g with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact add_nonneg (add_nonneg (Work.Spaces.HkNorm_nonneg α k _)
      (mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)))
      (Work.Spaces.HkNorm_nonneg α k _)
  have hB0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
  have hC0 : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k _
  have hAle : Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Construction.PhiTil α g Ψ))
      ≤ X := by
    rw [hXdef]
    exact le_trans (le_add_of_nonneg_right hB0) (le_add_of_nonneg_right hC0)
  have hαDzX : α * Work.Spaces.HkNorm α k
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ))) ≤ Cn * X := by
    rw [hXdef]; exact hN4
  have hΦX : Work.Spaces.HkNorm α k Φ ≤ Cn * (Cn * X) :=
    le_trans hN1 (le_trans (mul_le_mul_of_nonneg_left hN3 hCn0)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAle hCn0) hCn0))
  have hnormA : Work.Spaces.HkNorm α k A ≤ Real.sqrt Cm * (Cn * (Cn * X)) := by
    have hs : Work.Spaces.HkSq α k A ≤ Cm * Work.Spaces.HkSq α k Φ :=
      ((hCm α Φ hα hα1 hSmΦ).2.2 hmΦ).2.2.2
    have h1 : Work.Spaces.HkNorm α k A ≤ Real.sqrt Cm * Work.Spaces.HkNorm α k Φ := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← Real.sqrt_mul hCm0]
      exact Real.sqrt_le_sqrt hs
    exact le_trans h1 (mul_le_mul_of_nonneg_left hΦX (Real.sqrt_nonneg Cm))
  have hnormA' : Work.Spaces.HkNorm α k A' ≤ Cn * (Cn * X) := by
    have h1 : Cn * α * Work.Spaces.HkNorm α k
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ)))
        = Cn * (α * Work.Spaces.HkNorm α k
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ)))) := by ring
    calc Work.Spaces.HkNorm α k A'
        ≤ Cn * α * Work.Spaces.HkNorm α k
            (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ))) := hN2
      _ = Cn * (α * Work.Spaces.HkNorm α k
            (Work.Spaces.Dz (Work.Spaces.pth (Work.Construction.PhiTil α g Ψ)))) := h1
      _ ≤ Cn * (Cn * X) := mul_le_mul_of_nonneg_left hαDzX hCn0
  have hnormC : Work.Spaces.HkNorm α k Cc ≤ Cn * X :=
    le_trans hN3 (mul_le_mul_of_nonneg_left hAle hCn0)
  have hnorm4A : Work.Spaces.HkNorm α k (fun z θ => (4 : ℝ) * A z θ)
      ≤ 4 * (Real.sqrt Cm * (Cn * (Cn * X))) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k 4 hSmA.forall]
    norm_num
    exact hnormA
  have hnorm2A' : Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ)
      ≤ 2 * (Cn * (Cn * X)) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k 2 hSmA'.forall]
    norm_num
    exact hnormA'
  have htri1 : Work.Spaces.HkNorm α k
        (fun z θ => (4 : ℝ) * A z θ + ((2 : ℝ) * A' z θ + Cc z θ))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (fun z θ => (4 : ℝ) * A z θ)
          + Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ + Cc z θ)) :=
    Work.FTS.EllipticEst.HkNorm_add_le α k hSm4A.forall hSm2A'C.forall hm4A hm2A'C
  have htri2 : Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ + Cc z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ)
          + Work.Spaces.HkNorm α k Cc) :=
    Work.FTS.EllipticEst.HkNorm_add_le α k hSm2A'.forall hSmC.forall hm2A' hmPth
  have hsqeq : Work.Spaces.HkSq α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
      = Work.Spaces.HkSq α k (fun z θ => (4 : ℝ) * A z θ + ((2 : ℝ) * A' z θ + Cc z θ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α k
      (fun z θ hz hθ0 hθ1 => (hAgree z θ hz hθ0 hθ1).symm)
  refine ⟨⟨smoothOpen_rop_phiTil_gen hα hg hO, hmRop⟩, ?_⟩
  have heq : Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
      = Work.Spaces.HkNorm α k
          (fun z θ => (4 : ℝ) * A z θ + ((2 : ℝ) * A' z θ + Cc z θ)) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsqeq]
  rw [heq]
  calc Work.Spaces.HkNorm α k (fun z θ => (4 : ℝ) * A z θ + ((2 : ℝ) * A' z θ + Cc z θ))
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (fun z θ => (4 : ℝ) * A z θ)
          + Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ + Cc z θ)) := htri1
    _ ≤ Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X)))
          + Real.sqrt 2 * (2 * (Cn * (Cn * X)) + Cn * X)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hnorm4A ?_) (Real.sqrt_nonneg 2)
        calc Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ + Cc z θ)
            ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k (fun z θ => (2 : ℝ) * A' z θ)
                + Work.Spaces.HkNorm α k Cc) := htri2
          _ ≤ Real.sqrt 2 * (2 * (Cn * (Cn * X)) + Cn * X) := by
              refine mul_le_mul_of_nonneg_left (add_le_add hnorm2A' hnormC) (Real.sqrt_nonneg 2)
    _ ≤ (2 * (4 * Real.sqrt Cm * Cn * Cn + 2 * Cn * Cn + Cn)) * X := by
        have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have h2le : Real.sqrt 2 ≤ 2 := by
          have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          nlinarith [Real.sqrt_nonneg 2, h]
        have hsplit : Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X)))
              + Real.sqrt 2 * (2 * (Cn * (Cn * X)) + Cn * X))
            = Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X))))
              + 2 * (2 * (Cn * (Cn * X)) + Cn * X) := by
          rw [show Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X)))
                + Real.sqrt 2 * (2 * (Cn * (Cn * X)) + Cn * X))
              = Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X))))
                + (Real.sqrt 2 * Real.sqrt 2) * (2 * (Cn * (Cn * X)) + Cn * X) from by ring,
            h22]
        rw [hsplit, show (2 * (4 * Real.sqrt Cm * Cn * Cn + 2 * Cn * Cn + Cn)) * X
            = (8 * Real.sqrt Cm * Cn * Cn + 4 * Cn * Cn + 2 * Cn) * X from by ring]
        have hstep : Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X))))
            ≤ 8 * Real.sqrt Cm * Cn * Cn * X := by
          have h1 : Real.sqrt 2 * Real.sqrt Cm ≤ 2 * Real.sqrt Cm :=
            mul_le_mul_of_nonneg_right h2le (Real.sqrt_nonneg Cm)
          have h2 : 4 * (Real.sqrt 2 * Real.sqrt Cm) * (Cn * (Cn * X))
              ≤ 4 * (2 * Real.sqrt Cm) * (Cn * (Cn * X)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by positivity)
          have h3 : 4 * (2 * Real.sqrt Cm) * (Cn * (Cn * X))
              = 8 * Real.sqrt Cm * Cn * Cn * X := by ring
          have h4 : Real.sqrt 2 * (4 * (Real.sqrt Cm * (Cn * (Cn * X))))
              = 4 * (Real.sqrt 2 * Real.sqrt Cm) * (Cn * (Cn * X)) := by ring
          rw [h4]
          rw [h3] at h2
          exact h2
        linarith [hstep]

end Work.FTS.ClassC
