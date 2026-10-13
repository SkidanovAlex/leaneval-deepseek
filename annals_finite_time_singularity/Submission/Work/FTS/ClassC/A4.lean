/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.A4` — the elliptic packages `EllPkgGo` and `EllPkgK` (design (A), item A4)

Item A4 of the design: from a solution `Ψ` of the level-`K` class
(`Work.FTS.EllExist.EllClassOk K α g Ψ`) over a profile `g` of the linear class `ClassC α g`,
obtain the two packages the calculus consumes,

* `Work.FTS.VocabO.EllPkgGo α Ce g Ψ` — the `ℋ⁴`-package (`sol`, `smooth`, the three operator
  slots `ℛ`, `U/sin 2θ`, `V` with `‖·‖_{ℋ⁴} ≤ Ce‖g‖_{ℋ⁴}`, the trace `vanishU`, and the sup-slot
  `V^{th}` with the `α^{-1/2}` gain), which is what the a-priori/coercivity chapter asks for;
* `EllPkgK α 6 Ce g Ψ` (`FTS/ClassC/Defs.lean`) — the same three operator slots at level `6`,
  which is what the level-six rows of the persistence chapter ask for.

The bookkeeping is isolated in `ellPkgK_of_slots_le` and `ellPkgGo_of_slots_le`, which take the
slot estimates **at a fixed constant** `C` (the `_le` predicates below) and return the packages at
that same `C`; the `∃ C`-forms `SlotK`, `VthSlot` are the packaged statements proved in the sibling
modules `Work.FTS.ClassC.ropTransfer_classC` (level `7`) / `ropTransferGen` (general solution
level), `Work.FTS.ClassC.uopTransferGen`, `Work.FTS.ClassC.vopTransferGen` and
`Work.FTS.ClassC.vthTransfer_classC`; the names `uopTransfer_classC`/`vopTransfer_classC` are kept
as documented aliases of the `*Gen` proofs.

## The two solution levels

Each slot estimate carries *two* level parameters: the level `k` of the norm, and the level `K` of
the solution class it is stated over.  The `ℛ`/`U`/`V` operators cost one order of honesty
(`Rop` and `U` contain one extra `D_z` modulo `sin 2θ`), so the level-`k` slot needs
`K ≥ k + 2`:

* the level-`4` slots are stated over `EllClassOk 7`;
* the level-`6` slots over `EllClassOk 8` (lead ruling of 2026-10-08 09:50: the frozen class
  supplied the traces only up to `j = 6`, while the top summand `α·D_z⁷Ξ/sin 2θ` of the `U`-slot
  needs the `j = 7` trace for every `z`).

`ClassC` therefore carries both `HkMem α 7 g`/`BdryTraces α 6 g` and the two extra fields
`HkMem α 8 g`/`BdryTraces α 7 g`; `EllClassOk 8` also descends to `EllClassOk 7` via
`ellClassOk_mono`, which is what lets `Main` feed the level-`4` slots from the level-`8`
existence node.

Two clauses are *not* hypotheses and are proved here from the class:

* the law `IsBslSolPos α g Ψ` (from `IsBslSol α g Ψ` of `EllClassOk`);
* the trace clause `vanishU` (`vanishU_of_classOk`), which comes from the two Dirichlet values of
  `Ψ` — exactly as in `FTS/EllSol/EllPkgGo.lean`.

Everything in this file is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.EllPkgGo
import Submission.Work.FTS.EllSol.PkgK5.Fstar_DzIter_le_honest

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

/-! ## Monotonicity of the solution class in the level -/

/-- **`EllClassOk` is monotone in the level**: lowering the level only weakens the `HkMem`
requirements. -/
theorem ellClassOk_mono {α : ℝ} {K l : ℕ} (hlK : l ≤ K) {g Ψ : Fn}
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ) : Work.FTS.EllExist.EllClassOk l α g Ψ :=
  ⟨h.1, h.2.1, Work.FTS.EllSol.PkgK5.EllWeakPos_descend hlK h.2.2⟩

/-! ## The trace clause of the `U`-slot, from the Dirichlet data -/

/-- `EllResid α g Ψ` vanishes identically at `θ = 0` when `Ψ` does. -/
theorem EllResid_at_zero {α : ℝ} {g Ψ : Fn} (h : ∀ z, Ψ z 0 = 0) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z 0 = 0 := by
  rw [Work.Elliptic.EllResid]
  simp [h z]

/-- `EllResid α g Ψ` vanishes identically at `θ = π/2` when `Ψ` does. -/
theorem EllResid_at_pi_half {α : ℝ} {g Ψ : Fn} (h : ∀ z, Ψ z (π / 2) = 0) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z (π / 2) = 0 := by
  rw [Work.Elliptic.EllResid]
  simp only [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
  simp [h z]

/-- `∂_z` of a function vanishing identically at an angle vanishes there. -/
theorem pz_eq_zero_of_forall_eq_zero {f : Fn} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0) (z : ℝ) :
    Work.Spaces.pz f z θ₀ = 0 := by
  have hfun : (fun z' : ℝ => f z' θ₀) = fun _ => (0 : ℝ) := funext h
  simp only [Work.Spaces.pz, hfun]
  exact deriv_const z (0 : ℝ)

/-- **The `vanishU` clause of `EllPkgGo` holds for every level-`7` solution** (no trace
hypothesis is needed: it comes from the two Dirichlet values of `Ψ`). -/
theorem vanishU_of_classOk {α : ℝ} {g Ψ : Fn} (h : Work.FTS.EllExist.EllClassOk 7 α g Ψ) :
    Work.Spaces.VanishTheta
      (Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ)) := by
  rw [Work.FTS.EllipticEst.Uop_PhiTil_eq]
  have h0 : ∀ z, Work.Elliptic.EllResid α g Ψ z 0 = 0 := fun z => EllResid_at_zero h.1.2.1 z
  have hπ : ∀ z, Work.Elliptic.EllResid α g Ψ z (π / 2) = 0 :=
    fun z => EllResid_at_pi_half h.1.2.2.1 z
  constructor
  · intro z
    have h1 := pz_eq_zero_of_forall_eq_zero h0 z
    simp only [Work.FTS.EllipticEst.Uop, h0 z, h1]
    ring
  · intro z
    have h1 := pz_eq_zero_of_forall_eq_zero hπ z
    simp only [Work.FTS.EllipticEst.Uop, hπ z, h1]
    ring

/-! ## The four slot estimates, at a fixed constant -/

/-- The `ℛ`-slot estimate at level `k` over the solution level `K`, with constant `C`. -/
def RopSlotLe (k K : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk K α g Ψ →
    Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ)) ∧
    Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
      ≤ C * Work.Spaces.HkNorm α k g

/-- The `U/sin 2θ`-slot estimate at level `k` over the solution level `K`, with constant `C`. -/
def UopSlotLe (k K : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk K α g Ψ →
    Work.FTS.VocabO.HQo α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ) ∧
    Work.Spaces.HkNorm α k (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
      ≤ C * Work.Spaces.HkNorm α k g

/-- The `V`-slot estimate at level `k` over the solution level `K`, with constant `C`. -/
def VopSlotLe (k K : ℕ) (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk K α g Ψ →
    Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ)) ∧
    Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
      ≤ C * Work.Spaces.HkNorm α k g

/-- The `V^{th}`-slot estimate (level `4`, solution level `7`), with constant `C`. -/
def VthSlotLe (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk 7 α g Ψ →
    Work.FTS.VocabO.CoefThMem 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ)) ∧
    Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g

/-- The three slot estimates at level `k` over the solution level `K`, some constant. -/
def SlotK (k K : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ RopSlotLe k K C ∧ UopSlotLe k K C ∧ VopSlotLe k K C

/-- The level-`4` slots over `EllClassOk 7`. -/
def SlotK4 : Prop := SlotK 4 7

/-- The level-`6` slots over `EllClassOk 8`. -/
def SlotK6 : Prop := SlotK 6 8

/-- The `V^{th}`-slot, some constant. -/
def VthSlot : Prop := ∃ C : ℝ, 0 < C ∧ VthSlotLe C

/-! ## The two packages -/

/-- **A4, level `k`: the package `EllPkgK α k`** from the three slot estimates at the constant
`C`. -/
theorem ellPkgK_of_slots_le (k K : ℕ) (C : ℝ)
    (hR : RopSlotLe k K C) (hU : UopSlotLe k K C) (hV : VopSlotLe k K C) :
    ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
      Work.FTS.EllExist.EllClassOk K α g Ψ → EllPkgK α k C g Ψ := by
  intro α g Ψ hα hα4 hg h
  exact ⟨Work.FTS.StrongGlobal.IsBslSol.toPos h.1, h.2.1,
    hR α g Ψ hα hα4 hg h, hU α g Ψ hα hα4 hg h, hV α g Ψ hα hα4 hg h⟩

/-- **A4, level `k`, `∃ C`-form.** -/
theorem ellPkgK_of_slots (k K : ℕ) (h : SlotK k K) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 →
      ClassC α g → Work.FTS.EllExist.EllClassOk K α g Ψ → EllPkgK α k Ce g Ψ := by
  obtain ⟨C, hC, hR, hU, hV⟩ := h
  exact ⟨C, hC, fun α g Ψ hα hα4 hg h =>
    ellPkgK_of_slots_le k K C hR hU hV α g Ψ hα hα4 hg h⟩

/-- **A4, level `4`: the package `EllPkgGo`** from the three level-`4` slot estimates and the
sup-slot at the constant `C`. -/
theorem ellPkgGo_of_slots_le (C : ℝ)
    (hR : RopSlotLe 4 7 C) (hU : UopSlotLe 4 7 C) (hV : VopSlotLe 4 7 C) (hT : VthSlotLe C) :
    ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
      Work.FTS.EllExist.EllClassOk 7 α g Ψ → Work.FTS.VocabO.EllPkgGo α C g Ψ := by
  intro α g Ψ hα hα4 hg h
  exact ⟨h.1, h.2.1, hR α g Ψ hα hα4 hg h, hU α g Ψ hα hα4 hg h, hV α g Ψ hα hα4 hg h,
    vanishU_of_classOk h, hT α g Ψ hα hα4 hg h⟩

/-- **A4, level `4`, `∃ C`-form.** -/
theorem ellPkgGo_of_slots (hK : SlotK4) (hVth : VthSlot) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 →
      ClassC α g → Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      Work.FTS.VocabO.EllPkgGo α Ce g Ψ := by
  obtain ⟨C, hC, hR, hU, hV⟩ := hK
  obtain ⟨CT, hCT, hT⟩ := hVth
  refine ⟨C + CT, by positivity, fun α g Ψ hα hα4 hg h => ?_⟩
  have hg4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαpow : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  obtain ⟨hRm, hRb⟩ := hR α g Ψ hα hα4 hg h
  obtain ⟨hUm, hUb⟩ := hU α g Ψ hα hα4 hg h
  obtain ⟨hVm, hVb⟩ := hV α g Ψ hα hα4 hg h
  obtain ⟨hTm, hTb⟩ := hT α g Ψ hα hα4 hg h
  have hCl : C ≤ C + CT := by linarith
  have hTl : CT ≤ C + CT := by linarith
  have h1 : C * Work.FTS.Nonlin.Xn α g ≤ (C + CT) * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right hCl hg4
  have h2 : CT * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g
      ≤ (C + CT) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTl hαpow) hg4
  exact ⟨h.1, h.2.1, ⟨hRm, le_trans hRb h1⟩, ⟨hUm, le_trans hUb h1⟩, ⟨hVm, le_trans hVb h1⟩,
    vanishU_of_classOk h, ⟨hTm, le_trans hTb h2⟩⟩

/-! ## Monotonicity of the packages in the constant -/

/-- `EllPkgK` is monotone in the constant. -/
theorem EllPkgK_mono {α : ℝ} {k : ℕ} {Ce Ce' : ℝ} {g Φg : Fn}
    (h : EllPkgK α k Ce g Φg) (hle : Ce ≤ Ce') : EllPkgK α k Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩⟩ := h
  have hgnn : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hmon : ∀ X : ℝ, X ≤ Ce * Work.Spaces.HkNorm α k g →
      X ≤ Ce' * Work.Spaces.HkNorm α k g :=
    fun X hX => le_trans hX (mul_le_mul_of_nonneg_right hle hgnn)
  exact ⟨h1, h2, ⟨hRm, hmon _ hRb⟩, ⟨hUm, hmon _ hUb⟩, ⟨hVm, hmon _ hVb⟩⟩

/-- `EllPkgGo` is monotone in the constant (`0 < α` is needed only to keep the
`α^{-1/2}`-factor nonnegative). -/
theorem EllPkgGo_mono {α Ce Ce' : ℝ} {g Φg : Fn} (hα : 0 < α)
    (h : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hle : Ce ≤ Ce') :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩, hv, ⟨hTm, hTb⟩⟩ := h
  have hgnn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  refine ⟨h1, h2, ⟨hRm, ?_⟩, ⟨hUm, ?_⟩, ⟨hVm, ?_⟩, hv, ⟨hTm, ?_⟩⟩
  · exact le_trans hRb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hUb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hVb (mul_le_mul_of_nonneg_right hle hgnn)
  · refine le_trans hTb ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hαp) hgnn

end Work.FTS.ClassC
