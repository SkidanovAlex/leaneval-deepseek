/-
# `Comm2_succ`: the `Comm2`-package climbs one level under `HkIPStep`

The algebraic package `Work.FTS.CoercivityFix.Assembly.Comm2 α n IP`
(`Assembly/Defs.lean`) carries the four *membership-free / level-explicit* facts about an
inner product `IP` that the corrected induction of `Submission/Work/FTS/CoercivityFix`
consumes:

* `congr` — congruence in the first argument on the **open** quadrant `Qd`, with **no**
  regularity hypothesis (derivatives are local and `Qd` is open);
* `add`   — additivity in the first argument, on the level-`n` regularity class `RegQ α n`;
* `dthC`  — the *exact* commutation `D_θ (Lhat f) = Lhat (D_θ f)`;
* `dzC`   — the `D_z`-commutator identity `D_z (Lhat f) = Lhat (D_z f) + Ê₂ f`.

This file proves that the paper's recursion
`HkIPStep c₁ c₂ IP = IP + c₁ IP(D_θ·, D_θ·) + c₂ IP(D_z·, D_z·)` (`tex 686`) inherits all
four clauses **one level up**:

  `Comm2 α n IP → Comm2 α (n+1) (HkIPStep c₁ c₂ IP)`.

The two commutator clauses mention neither `n` nor `IP` (they are statements about `Lhat`
alone), so they are inherited *verbatim*.  The two pairing clauses are inherited by

* the two derivative-linearity facts on the open quadrant `Qd` —
  `D_θ` and `D_z` are additive there because the slices of a `SmoothQuad` function are
  differentiable (`LocData.SmoothQuad.differentiableAt_slice_*`), and `deriv_add` needs
  nothing else;
* the two derivative-locality facts on `Qd` — functions agreeing on the open quadrant have
  the same `D_θ` and `D_z` there (`Filter.EventuallyEq.deriv_eq`);
* the *descent* of the regularity class `RegQ α (n+1) f → RegQ α n f` (`regQ_mono`) and its
  closure under the two derivatives (`RegQ_dth`, `RegQ_dz`), which is what turns the
  level-`n` additivity clause of `IP` into the level-`(n+1)` additivity clause of
  `HkIPStep`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Locality and linearity of the two derivatives on the open quadrant

The open quadrant `Qd = (0,∞) × (0,π/2)` is `Work.Construction.Qd`, definitionally
`Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)`.  Both facts are *pointwise on `Qd`*, which is exactly the
form in which the `congr` clause of `Comm2` is stated. -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there:
the derivative is local and `Qd` is open in the `θ`-variable. -/
private lemma Dth_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' ⟨hz, hθ'⟩
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
private lemma Dz_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ ⟨hz', hθ⟩
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-- `D_θ` is additive on the open quadrant, for `SmoothQuad` functions. -/
private lemma Dth_add_Qd {f₁ f₂ : Fn} (h₁ : Work.FTS.LocData.SmoothQuad f₁)
    (h₂ : Work.FTS.LocData.SmoothQuad f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (f₁ + f₂) z θ = Work.Spaces.Dth f₁ z θ + Work.Spaces.Dth f₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have hd : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f →
      DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    fun f hf => hf.differentiableAt_slice_DthIter 0 hz hθ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' => (f₁ + f₂) z θ') = (fun θ' => f₁ z θ') + (fun θ' => f₂ z θ') from rfl,
    deriv_add (hd f₁ h₁) (hd f₂ h₂)]
  ring

/-- `D_z` is additive on the open quadrant, for `SmoothQuad` functions. -/
private lemma Dz_add_Qd {f₁ f₂ : Fn} (h₁ : Work.FTS.LocData.SmoothQuad f₁)
    (h₂ : Work.FTS.LocData.SmoothQuad f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (f₁ + f₂) z θ = Work.Spaces.Dz f₁ z θ + Work.Spaces.Dz f₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have hd : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f →
      DifferentiableAt ℝ (fun z' => f z' θ) z :=
    fun f hf => hf.differentiableAt_slice_mixed 0 0 hz hθ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [show (fun z' => (f₁ + f₂) z' θ) = (fun z' => f₁ z' θ) + (fun z' => f₂ z' θ) from rfl,
    deriv_add (hd f₁ h₁) (hd f₂ h₂)]
  ring

/-! ## The induction step of the package -/

/-- **`Comm2` climbs one level under the paper's recursion `HkIPStep c₁ c₂`.**  The two
commutator clauses are inherited verbatim (they mention neither the level `n` nor the inner
product), and the congruence/additivity clauses are transported through the two
derivative-locality / derivative-linearity facts above. -/
theorem Comm2_succ (α : ℝ) (hα : 0 < α) (n : ℕ) {IP : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {c₁ c₂ : ℝ} (hc : Work.FTS.CoercivityFix.Assembly.Comm2 α n IP) :
    Work.FTS.CoercivityFix.Assembly.Comm2 α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  refine ⟨?congr, ?add, hc.dthC, hc.dzC⟩
  case congr =>
    intro f f' g hfg
    have e0 := hc.congr f f' g hfg
    have e1 := hc.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Dth_congr_Qd hfg)
    have e2 := hc.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  case add =>
    intro f₁ f₂ g hf₁ hf₂ hg
    have h₁ : Work.FTS.Nonlin.RegQ α n f₁ :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hf₁ (Nat.le_succ n)
    have h₂ : Work.FTS.Nonlin.RegQ α n f₂ :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hf₂ (Nat.le_succ n)
    have h₃ : Work.FTS.Nonlin.RegQ α n g :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hg (Nat.le_succ n)
    have e0 := hc.add f₁ f₂ g h₁ h₂ h₃
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [hc.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (fun z θ hzθ => Dth_add_Qd hf₁.1 hf₂.1 z θ hzθ)]
      exact hc.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hf₁)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hf₂)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hg)
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [hc.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (fun z θ hzθ => Dz_add_Qd hf₁.1 hf₂.1 z θ hzθ)]
      exact hc.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hf₁)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hf₂)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

end Work.FTS.CoercivityFix.Assembly
