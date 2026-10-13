/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N0_N_Transport_pt_le` — the pointwise bounds on the right-hand side of the `ε`-scheme

For a family `g` of approximate solutions of the modulated scheme, the interface `EpsDecay`
provides a majorant `Maj` of the *slots* of the projected slice `W = slice (JfamP ρ ε g) τ` and of
the three elliptic blocks `Rop`, `Uop/sin 2θ`, `Vop` of the residual stream function; together
with the class `ClassC α W` and the two size bounds `Xn α W ≤ C₀ α²`, `Xn6 α W ≤ B`, this bounds
the three blocks of the right-hand side **pointwise**, with the angular weight `1/sin 2θ`:

* `|N₀ α (F_* + W) W| ≤ C (1+C₀) (1+B) / sin 2θ`,
* `|N α (F_* + W) Φg| ≤ C (1+C₀) (1+B) / sin 2θ`,
* `|Transport W| ≤ C (1+C₀) (1+B) / sin 2θ`.

The `1/sin 2θ` is exactly what the pointwise route affords: every occurrence of `∂_θ` in the
three blocks carries the factor `sin 2θ` (`D_θ = sin 2θ ∂_θ`), and the `z`-direction is
controlled by `∂_z`.  The only non-local input is `L₁₂(W)(z)`, bounded by `C · Xn α W ≤ C C₀ α²`
(`L12_abs_le_Xn`); the reference profile contributes `L₁₂(F_*)(z) = 2α/(1+z)` and
`FK(F_*)(z) = α · 2z/(1+z)²`.

The proof is assembled from the three block bounds `pt_N0_le`, `pt_N_le`, `pt_Transport_le`
(module `E5Aux2/PTblocks.lean`) applied to the explicit data extracted from the interface
(`pt_EpsDecay_slots`, `pt_Xi_slots`, `pt_FK_le`, module `E5Aux2/PTgadgets.lean`).

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsWPBounds
import Submission.Work.FTS.StrongEps.E5Aux2.PTgadgets
import Submission.Work.FTS.StrongEps.E5Aux2.PTblocks

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem N0_N_Transport_pt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
        {ε τ C₀ B : ℝ} {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ B →
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ|
          ≤ C * (1 + C₀) * (1 + B) / Real.sin (2 * θ)) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ)
            z θ| ≤ C * (1 + C₀) * (1 + B) / Real.sin (2 * θ)) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Coercivity.Transport (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            z θ| ≤ C * (1 + C₀) * (1 + B) / Real.sin (2 * θ)) := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongEps.L12_abs_le_Xn
  obtain ⟨C7, hC7nn, hC7⟩ := Work.FTS.StrongEps.FK_abs_le_of_classC
  refine ⟨1000 * (CL + 1) + (30000 + 200 * C7) + 4, by linarith, ?_⟩
  intro α hαι ρ Φs E ε τ C₀ B g Maj hDec hC hXn hB
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  -- the nonnegativity of the two interface constants
  have hC₀0 : 0 ≤ C₀ := by
    have h1 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have h2 : 0 ≤ C₀ * α ^ 2 := le_trans h1 hXn
    by_contra hlt
    push_neg at hlt
    have h3 : 0 < α ^ 2 := pow_pos hα0 2
    have h4 : C₀ * α ^ 2 < 0 := mul_neg_of_neg_of_pos hlt h3
    linarith
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  -- the slot data of the interface (extracted before the `set`s rewrite it)
  obtain ⟨-, hWval, hWDz, hWDth, hSlotR, hSlotU, hSlotV⟩ := pt_EpsDecay_slots hDec
  -- the projected slice, the residual stream function and the full profile
  set W : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hWdef
  set Φg : ℝ → ℝ → ℝ :=
    Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ
    with hΦgdef
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ with hFdef
  have hFdec : F = fun z θ => Work.Construction.Fstar α z θ + W z θ := by
    rw [hFdef, hWdef]
    funext z θ
    rfl
  have hCS : Work.FTS.EllipticEst.SmoothOpen W := hC.reg
  have hWC4 : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hCS 4 (by norm_num) hC.mem
  have hCS4 : Work.FTS.VocabO.HQo α 4 W := ⟨hCS, hWC4⟩
  have hL12W : ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12 W z| ≤ CL * (C₀ * α ^ 2) := by
    intro z hz
    refine le_trans (hCL α hα0 W hCS4 z hz.le) ?_
    exact mul_le_mul_of_nonneg_left hXn hCLpos.le
  have hFKW : ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK W z| ≤ C7 * B := hC7 α B hαι hC hB
  have hΞ := pt_Xi_slots hαι hCS hWC4 hSlotR hSlotU hSlotV
  -- the three blocks
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    refine le_trans (pt_N0_le hαι hC₀0 hB0 hCLpos hCS hFdec hWval hWDz hWDth hL12W
      z hz θ hθ) ?_
    have hs2pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    apply div_le_div_of_nonneg_right _ hs2pos.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1000 * (CL + 1)
        ≤ 1000 * (CL + 1) + (30000 + 200 * C7) + 4) (by linarith))
      (by linarith)
  · intro z hz θ hθ
    refine le_trans (pt_N_le hαι hC₀0 hB0 hC7nn hCS hWC4 hFdec hWval hWDz hWDth hFKW hΞ
      z hz θ hθ) ?_
    have hs2pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    apply div_le_div_of_nonneg_right _ hs2pos.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (30000 + 200 * C7)
        ≤ 1000 * (CL + 1) + (30000 + 200 * C7) + 4) (by linarith))
      (by linarith)
  · intro z hz θ hθ
    refine le_trans (pt_Transport_le hC₀0 hB0 hWDth z hz θ hθ) ?_
    have hs2pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    apply div_le_div_of_nonneg_right _ hs2pos.le
    have hCL1 : 0 ≤ 1000 * (CL + 1) := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [hCL1, hC7nn] : (3 : ℝ)
        ≤ 1000 * (CL + 1) + (30000 + 200 * C7) + 4) (by linarith))
      (by linarith)

end Work.FTS.StrongEps.E5Aux2
