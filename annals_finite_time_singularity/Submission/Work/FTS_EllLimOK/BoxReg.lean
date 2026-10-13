/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxReg` — closed-box regularity of the Fatou limit

The uniqueness obligation `Defs3.ClosedUniq3` compares two jet-cluster-limits `Ψ`, `Ψ'` of the
same operator along the same sequence.  Both carry `Defs3.FatouPkg`, which constrains them only
on the **open** quadrant `Qd = (0,∞) × (0,π/2)` and through integral memberships whose weights
are *integrable* at the angular endpoints (`sin(2θ)^{-η}`, `η = 99/100 < 1`).

That is not enough to run the `θ`-energy method of the chapter (`Lzero_self_form`,
`Lzero_orthogonal`, `angQ_ge`): every one of those identities has a boundary term at `θ = 0`
proportional to the **one-sided limit** of the slice, which the memberships do not control.  The
tree has already established this phenomenon twice, by counterexample, for the analogous class
`EllipticEst.EllHyp` (whose `smooth` field is `SmoothInt`, with no control of the traces):

* `EllipticEst/Final/NOTES_energy1_inf_int_FALSE.md` — the energy identity with the boundary
  term dropped is **false** for `SmoothInt` data: a slice with value `0` at `θ = 0` but
  one-sided limit `≠ 0` satisfies all the hypotheses and violates the inequality;
* `EllipticEst/SmoothInt_rescope_blocker.md` — the same for the constrained slice Poincaré gap.

The repair in the tree was to move from `EllHyp` to the neighbourhood class `EllHypN`
(`SmoothNbhd`/`SmoothStrip`).  The limits produced by our Arzelà–Ascoli compactness argument are
**not** smooth, so the repair here is the finite-order analogue: the function is required to be
jointly `C²` on every **closed box** `[a,b] × [0,π/2]` with `0 < a ≤ b`.  This is the
closed-quadrant regularity that elliptic regularity gives for the paper's solutions, it is free
of the junk values of the extension off the quadrant (`ContDiffWithinAt` only tests points of
the box), and it is exactly what makes the boundary terms of the three angular identities
vanish.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The definition -/

/-- The closed box `[a,b] × [0,π/2]` (with `0 < a ≤ b`, so it is contained in the closed right
half-plane and bounded away from the degenerate line `z = 0`). -/
def cbox (a b : ℝ) : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc 0 (π / 2)

@[simp] theorem mem_cbox {a b z θ : ℝ} :
    (z, θ) ∈ cbox a b ↔ z ∈ Set.Icc a b ∧ θ ∈ Set.Icc 0 (π / 2) := Iff.rfl

/-- **Closed-box regularity**: on every box `[a,b] × [0,π/2]` with `0 < a ≤ b` the function is
jointly `C²`.  This is the finite-order substitute for the tree's closed-quadrant smoothness
(`Work.Spaces.SmoothNbhd` / `SmoothStrip`); see the module docstring for why the uniqueness
obligation cannot be proved without it. -/
def BoxReg (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ContDiffOn ℝ 2 (Function.uncurry Ψ) (cbox a b)

/-! ## The API -/

/-- **The slice at a fixed `z > 0` is `C²` on the closed interval `[0,π/2]`** — the hypothesis
consumed by `Work.FTS.EllipticEst.Lzero_self_form`, `Work.Elliptic.Lzero_orthogonal` and
`Work.FTS.EllipticEst.angQ_ge`. -/
theorem BoxReg.slice {Ψ : ℝ → ℝ → ℝ} (h : BoxReg Ψ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Icc 0 (π / 2)) := by
  have hbox := h z (z + 1) hz (by linarith)
  have hcont : ContDiffOn ℝ 2 (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Icc 0 (π / 2)) := by
    fun_prop
  refine hbox.comp hcont ?_
  intro θ hθ
  exact ⟨⟨le_rfl, by linarith⟩, hθ⟩

/-- **`BoxReg` of the pointwise difference** (the difference of two jet-limits, the object of the
uniqueness obligation). -/
theorem BoxReg.sub {Ψ Φ : ℝ → ℝ → ℝ} (hΨ : BoxReg Ψ) (hΦ : BoxReg Φ) :
    BoxReg (fun z θ => Ψ z θ - Φ z θ) := by
  intro a b ha hab
  have h1 : Function.uncurry (fun z θ : ℝ => Ψ z θ - Φ z θ)
      = (Function.uncurry Ψ) - (Function.uncurry Φ) := by
    funext p
    simp [Function.uncurry]
  rw [h1]
  exact (hΨ a b ha hab).sub (hΦ a b ha hab)

/-- **`BoxReg` is joint `C²` at every interior point of the quadrant** (the local form used by
every differentiation under the `θ`-integral below). -/
theorem BoxReg.contDiffAt {Ψ : ℝ → ℝ → ℝ} (h : BoxReg Ψ) {p : ℝ × ℝ}
    (hp : p.1 ∈ Set.Ioi (0 : ℝ) ∧ p.2 ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry Ψ) p := by
  set a : ℝ := p.1 / 2 with ha
  set b : ℝ := 2 * p.1 with hb
  have hp1 : 0 < p.1 := hp.1
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hbox := h a b ha0 hab
  have hmem : p ∈ Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · rw [ha]; linarith
    · rw [hb]; linarith
  have hopen : IsOpen (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo.prod isOpen_Ioo
  refine hbox.contDiffAt (Filter.mem_of_superset (hopen.mem_nhds hmem) ?_)
  intro q hq
  exact ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩

/-- **`BoxReg` implies joint `C²` on the open quadrant**. -/
theorem BoxReg.contDiffOn_Qd {Ψ : ℝ → ℝ → ℝ} (h : BoxReg Ψ) :
    ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd :=
  fun p hp => (h.contDiffAt ⟨hp.1, hp.2⟩).contDiffWithinAt

end Work.FTS_EllLimOK
