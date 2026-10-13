/-
# The `θ`-slice model of the `D_z`-commutator defect `E₂`

Objects used by the proof of `Work.Coercivity.E2fun_slice_dichotomy`.

The pointwise identity `Work.Coercivity.CommutZ.CommutZ_pointwise_E2` writes the defect

  `E₂(z,θ) = mm(z)·f(z,θ) + (3/2)·mm(z)·D_θ f(z,θ) + (Γ(θ)/c(α))·G(z)`

on the open quadrant.  We single out

* `E2smooth f` — the *smooth* part `A(z,θ) = mm(z)·f + (3/2)·mm(z)·D_θ f`, which is `C^∞`
  on the whole box `(-1,∞) × (-1, π/2+1)` on which `Spaces.SmoothNbhd f` demands smoothness
  of `f` (in particular it is `C^∞` near `θ = 0` and near `θ = π/2`), and
* `E2model α f = E2smooth f + (Γ(θ)/c α)·Gfun f` — the model of `E₂`, which agrees with `E₂`
  on the quadrant.

The angular factor `Γ(θ) = (sinθ·cos²θ)^{α/3}` is *not* smooth at the endpoints; near `θ=0`
it behaves like `θ^{α/3}` and near `θ=π/2` like `(π/2-θ)^{2α/3}`.  All the analytic
information about the slices is carried by the smooth part, and by the `θ`-jets
`E2jet`/`E2jetPure` of its `D`-iterates at the two endpoints.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Coercivity.CommutZAux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DzIterSmoothOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The model of the defect -/

/-- The open box on which `Spaces.SmoothNbhd` demands smoothness. -/
def E2box : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)

theorem isOpen_E2box : IsOpen E2box := isOpen_Ioi.prod isOpen_Ioo

/-- The *smooth part* of the defect `E₂`: `A(z,θ) = mm(z)·f(z,θ) + (3/2)·mm(z)·D_θ f(z,θ)`. -/
def E2smooth (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => CommutZ.mm z * f z θ + (3 / 2) * (CommutZ.mm z * Spaces.Dth f z θ)

/-- The `Γ`-part of the defect: `(Γ(θ)/c(α))·Gfun f z`. -/
def E2gamma (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (CommutZ.Gfun f z / Spaces.c α) * Spaces.Gam α θ

/-- The model of the defect: `E2smooth f + E2gamma α f`. -/
def E2model (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => E2smooth f z θ + E2gamma α f z θ

@[simp] theorem E2model_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    E2model α f z θ = E2smooth f z θ + E2gamma α f z θ := rfl

theorem E2gamma_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    E2gamma α f z θ = (CommutZ.Gfun f z / Spaces.c α) * Spaces.Gam α θ := rfl

/-- **The model agrees with the defect on the quadrant.** -/
theorem E2fun_eq_E2model (α : ℝ) (hc : Spaces.c α ≠ 0) (f : ℝ → ℝ → ℝ)
    (hf : Spaces.SmoothNbhd f) (hT : CommutZ.TailHyp f) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ, CommutZ.E2fun α f z θ = E2model α f z θ := by
  intro z hz θ hθ
  rw [CommutZ.CommutZ_pointwise_E2 α hc f hf hT z hz θ hθ]
  simp only [E2model, E2smooth, E2gamma]
  ring

/-! ## Smoothness of the smooth part on the box -/

theorem contDiffOn_mm_fst :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => CommutZ.mm p.1) E2box := by
  refine ContDiffOn.div ?_ ?_ ?_
  · exact contDiffOn_const.mul contDiffOn_fst
  · exact (contDiffOn_const.add contDiffOn_fst).pow 2
  · intro p hp
    have h1 : (-1 : ℝ) < p.1 := hp.1
    have : (0 : ℝ) < 1 + p.1 := by linarith
    positivity

/-- `E2smooth f` is `C^∞` on the box, whenever `f` is (`SmoothNbhd f`). -/
theorem contDiffOn_uncurry_E2smooth (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (E2smooth f)) E2box := by
  have hpth := Spaces.contDiffOn_uncurry_pth isOpen_E2box hf
  have hmm := contDiffOn_mm_fst
  have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) E2box :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => CommutZ.mm p.1 * f p.1 p.2) E2box :=
    hmm.mul hf
  have h2 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ =>
      (3 / 2 : ℝ) * (CommutZ.mm p.1 * (Real.sin (2 * p.2) * Spaces.pth f p.1 p.2))) E2box :=
    contDiffOn_const.mul (hmm.mul (hsin.mul hpth))
  have h := h1.add h2
  refine h.congr ?_
  intro p hp
  rfl

/-! ## The `θ`-jets of the smooth part at the two endpoints -/

/-- The `m`-th `θ`-jet at `e` of the smooth part of `D_z^j D_θ^i E₂` (the mixed terms). -/
def E2jet (f : ℝ → ℝ → ℝ) (i j m : ℕ) (e : ℝ) (z : ℝ) : ℝ :=
  iteratedDeriv m (fun θ => Spaces.mixed j i (E2smooth f) z θ) e

/-- The `m`-th `θ`-jet at `e` of the smooth part of `D_z^i E₂` (the pure terms). -/
def E2jetPure (f : ℝ → ℝ → ℝ) (i m : ℕ) (e : ℝ) (z : ℝ) : ℝ :=
  iteratedDeriv m (fun θ => Spaces.DzIter i (E2smooth f) z θ) e

end Work.Coercivity
