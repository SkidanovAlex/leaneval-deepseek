/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EComparison/E_slots_diff_le.lean`

The **final form of the `E`-comparison input** of the `EpsLocal` Picard estimate, in the *quadrant*
shape in which the slot identity is available (`EComparison.Slot_eq_of_source` compares the slots
of two class elements only on the open quadrant `0 < z`, `0 < θ < π/2`: `SmoothOpen` and
`IsBslSol` constrain nothing outside it).

What this module adds to `EComparison/Reduction.lean`:

* `HkNorm_congr_open` — the `ℋ^k`-norm only sees the values on the open quadrant, so the quadrant
  slot identity is exactly as good as an equality of functions;
* `slots_eq_of_source_quadrant` — the packaged quadrant form of `EComparison.Slot_eq_of_source`;
* `EllPkgK_R_diff_le_of_slots`, `EllPkgK_U_diff_le_of_slots`, `EllPkgK_V_diff_le_of_slots` — the
  three *Lipschitz slot inputs* with hypotheses that mention only the quadrant slot identity (no
  function equality), i.e. the shape the `epsW`-estimates of the Picard argument consume;
* `EllPkgK_R_diff_le`, `EllPkgK_U_diff_le`, `EllPkgK_V_diff_le` — the same three, **unconditional**
  except for `0 < α ≤ 1`, obtained by discharging the slot identity with the proved
  `EComparison.Slot_eq_of_source`.

*Convention.*  In `EpsLocal` the operator `E` is constrained by `hEll` only on the class
`ClassC α`, so the estimates below are unconditional *on that class* — which is exactly the
hypothesis set the fixed-point argument has for the `ε`-scheme's iterates.

*A remark on `α`.*  `EComparison.Slot_eq_of_source` (equivalently `HomClsSlotsZero`) carries
`0 < α ≤ 1`; the workspace does not yet have the general-`α` slot identity.  The three
`_of_slots` lemmas below take the quadrant slot identity as a hypothesis, so they are available
for every `α` for which that identity is known.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.StrongEps.EComparison.EllPkgCls_E_sub
import Submission.Work.FTS.StrongEps.EComparison.Slot_eq_of_source
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The `ℋ^k`-norm only sees the open quadrant -/

/-- **`HkNorm` is insensitive to changes on the boundary of the quadrant.**  Immediate from
`Work.FTS.EllipticEst.HkSq_congr_open` and the definition `HkNorm = √HkSq`. -/
theorem HkNorm_congr_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  simp only [Work.Spaces.HkNorm]
  rw [Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-! ## The quadrant form of the slot identity -/

/-- **The slots of two class elements with the same source agree on the open quadrant** — the
packaged form of `EComparison.Slot_eq_of_source` (which is the assembled
`EllPkgCls_sub` + `HomClsSlotsZero`). -/
theorem slots_eq_of_source_quadrant {α Ce : ℝ} {F Ψ₁ Ψ₂ : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (h₁ : EllPkgCls α Ce F Ψ₁) (h₂ : EllPkgCls α Ce F Ψ₂) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        SlotR α F Ψ₁ z θ = SlotR α F Ψ₂ z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        SlotU α F Ψ₁ z θ = SlotU α F Ψ₂ z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        SlotV α F Ψ₁ z θ = SlotV α F Ψ₂ z θ) := by
  obtain ⟨hR, hU, hV⟩ := Slot_eq_of_source hα hα1 h₁ h₂
  exact ⟨fun z θ hz hθ hθ' => hR z hz θ ⟨hθ, hθ'⟩,
    fun z θ hz hθ hθ' => hU z hz θ ⟨hθ, hθ'⟩,
    fun z θ hz hθ hθ' => hV z hz θ ⟨hθ, hθ'⟩⟩

/-! ## The three Lipschitz slot inputs, from the quadrant slot identity

The shape below is the one the `epsW`-estimates consume: `u`, `v` are two `ClassC` profiles (so
that the difference `u - v` is in the class and `hEll` applies to it), `E u - E v` is in the
packages' class (`EComparison.EllPkgCls_E_sub_of_theta`), and the *quadrant* identity of the slots
of `E u - E v` and `E (u - v)` is what the reduction produces. -/

/-- **The `R`-slot Lipschitz input** (quadrant form). -/
theorem EllPkgK_R_diff_le_of_slots {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hslot : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      SlotR α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) z θ
        = SlotR α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ)) z θ) :
    Work.Spaces.HkNorm α 6 (SlotR α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have h := ((hEll (fun z θ => u z θ - v z θ) huv).2.R).2
  rw [HkNorm_congr_open α 6 hslot]
  exact h

/-- **The `U`-slot Lipschitz input** (quadrant form). -/
theorem EllPkgK_U_diff_le_of_slots {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hslot : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      SlotU α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) z θ
        = SlotU α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ)) z θ) :
    Work.Spaces.HkNorm α 6 (SlotU α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have h := ((hEll (fun z θ => u z θ - v z θ) huv).2.U).2
  rw [HkNorm_congr_open α 6 hslot]
  exact h

/-- **The `V`-slot Lipschitz input** (quadrant form). -/
theorem EllPkgK_V_diff_le_of_slots {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hslot : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      SlotV α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) z θ
        = SlotV α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ)) z θ) :
    Work.Spaces.HkNorm α 6 (SlotV α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have h := ((hEll (fun z θ => u z θ - v z θ) huv).2.V).2
  rw [HkNorm_congr_open α 6 hslot]
  exact h

/-! ## Discharging the slot identity -/

/-- **The `Θ`-additivity needed by `EllPkgCls_E_sub_of_theta`**, from `EComparison.L12_sub_HkMem`
and the definition `Theta α F = (1/(4α)) sin(2θ) L₁₂(F)`. -/
theorem theta_sub_of_classC {α : ℝ} {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u)
    (hv : Work.FTS.ClassC.ClassC α v) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => u z θ - v z θ) z θ
        = Work.Construction.Theta α u z θ - Work.Construction.Theta α v z θ := by
  intro z hz θ
  have hmu : Work.Spaces.HkMem α 4 u :=
    Work.FTS.OpenPkg.HkMem_mono_open hu.reg 4 (by norm_num) hu.mem
  have hmv : Work.Spaces.HkMem α 4 v :=
    Work.FTS.OpenPkg.HkMem_mono_open hv.reg 4 (by norm_num) hv.mem
  have hL := L12_sub_HkMem hu.reg hv.reg hmu hmv z hz
  simp only [Work.Construction.Theta]
  rw [hL]
  ring

/-- **The `R`-slot Lipschitz input, unconditional on `ClassC` (for `0 < α ≤ 1`).** -/
theorem EllPkgK_R_diff_le_open {α Ce : ℝ} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hv : Work.FTS.ClassC.ClassC α v) :
    Work.Spaces.HkNorm α 6 (SlotR α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ) := classC_sub hu hv
  have hsub : EllPkgCls α Ce (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) :=
    EllPkgCls_E_sub_of_theta hEll hu hv (theta_sub_of_classC hu hv)
  exact EllPkgK_R_diff_le_of_slots hEll huv
    (slots_eq_of_source_quadrant hα hα1 hsub (EllPkgCls_of_pkg hEll huv)).1

/-- **The `U`-slot Lipschitz input, unconditional on `ClassC` (for `0 < α ≤ 1`).** -/
theorem EllPkgK_U_diff_le_open {α Ce : ℝ} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hv : Work.FTS.ClassC.ClassC α v) :
    Work.Spaces.HkNorm α 6 (SlotU α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ) := classC_sub hu hv
  have hsub : EllPkgCls α Ce (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) :=
    EllPkgCls_E_sub_of_theta hEll hu hv (theta_sub_of_classC hu hv)
  exact EllPkgK_U_diff_le_of_slots hEll huv
    (slots_eq_of_source_quadrant hα hα1 hsub (EllPkgCls_of_pkg hEll huv)).2.1

/-- **The `V`-slot Lipschitz input, unconditional on `ClassC` (for `0 < α ≤ 1`).** -/
theorem EllPkgK_V_diff_le_open {α Ce : ℝ} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hv : Work.FTS.ClassC.ClassC α v) :
    Work.Spaces.HkNorm α 6 (SlotV α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ) := classC_sub hu hv
  have hsub : EllPkgCls α Ce (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ) :=
    EllPkgCls_E_sub_of_theta hEll hu hv (theta_sub_of_classC hu hv)
  exact EllPkgK_V_diff_le_of_slots hEll huv
    (slots_eq_of_source_quadrant hα hα1 hsub (EllPkgCls_of_pkg hEll huv)).2.2

/-- **The three slot inputs, bundled**: what the `epsW`-Lipschitz estimate consumes from the
elliptic operator `E` at two `ClassC` profiles with the same (difference) source. -/
theorem E_slots_diff_le {α Ce : ℝ} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hv : Work.FTS.ClassC.ClassC α v) :
    Work.Spaces.HkNorm α 6 (SlotR α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
        ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) ∧
    Work.Spaces.HkNorm α 6 (SlotU α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
        ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) ∧
    Work.Spaces.HkNorm α 6 (SlotV α (fun z θ => u z θ - v z θ)
        (fun z θ => E u z θ - E v z θ))
        ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) :=
  ⟨EllPkgK_R_diff_le_open hα hα1 hEll hu hv, EllPkgK_U_diff_le_open hα hα1 hEll hu hv,
    EllPkgK_V_diff_le_open hα hα1 hEll hu hv⟩

end Work.FTS.StrongEps.EComparison
