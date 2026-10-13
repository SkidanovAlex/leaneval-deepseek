/-
  WilG4c — `StepEngAux`: the first auxiliary layer of the §5.4 engine instantiation.

  Two independent groups of facts, both needed by the production of `CurveData` for the
  shrunk pullback (`StepHigherPlan.md` §15.2):

  * `nearmax_exists_or_empty` — the *near-maximiser existence* that fires the implication of
    the sliced choice lemma `Work.WilG4c.CurveFamAlphaListPureSliced`: if the fibre supremum of
    the `L`-th directional derivative over the fibre `C^{|L|}`-locus is finite at `x`, then
    either the fibre locus is empty at `x` (in which case every near-maximality statement at `x`
    is vacuous) or a `2`-approximate maximiser exists.  The two cases are exactly what the
    assembly case-splits on.
  * `fin1_contDiffAt_at` and `fin1_norm_iteratedFDeriv_le` — the `ℝ ≃ₗᵢ (Fin 1 → ℝ)` transport
    of `ContDiffAt` and of the operator-norm bound, which turns the conclusion of `F1Affine`
    (a statement about functions of `Fin 1 → ℝ`) into the `ℝ`-valued form consumed by the
    engine `Work.WilkG4c.curve_bound` (whose curve lives on `ℝ`).
-/
import Mathlib
import Submission.Work.WilG4c.exists_nearmax_of_bdd
import Submission.Work.WilG4c.norm_iteratedFDeriv_deriv_le
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4a.f1affine_of_f1affine1

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The near-maximiser exists off the bad set -/

/-- **Either the fibre locus is empty, or a `2`-approximate maximiser exists.**  Given that the
values `|∂^L g|` over the fibre `C^{|L|}`-locus at `x` are bounded above, the fibre locus is
either empty at `x` — then every near-maximality assertion at the point `x` is vacuous — or it
contains a point `y` whose `|∂^L g|` is within the factor `2` of the whole fibre supremum.

This is the exact form of the hypothesis of the implication in the sliced choice lemma
`Work.WilG4c.CurveFamAlphaListPureSliced`; the "or empty" disjunct is what lets the assembly
avoid assuming that the fibre locus is nonempty (which would need `G1_generic_smooth`). -/
theorem nearmax_exists_or_empty {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    {x : ℝ}
    (hBdd : BddAbove ((fun y => |iteratedFDeriv ℝ L.length g (pt x y)
        (fun j => Pi.single (L.get j) 1)|) '' {y | y ∈ openCube n ∧
          ContDiffAt ℝ L.length g (pt x y)})) :
    (∃ y : Fin n → ℝ, y ∈ openCube n ∧ ContDiffAt ℝ L.length g (pt x y) ∧
      ∀ y' : Fin n → ℝ, y' ∈ openCube n → ContDiffAt ℝ L.length g (pt x y') →
        |iteratedFDeriv ℝ L.length g (pt x y') (fun j => Pi.single (L.get j) 1)| ≤
        2 * |iteratedFDeriv ℝ L.length g (pt x y) (fun j => Pi.single (L.get j) 1)|) ∨
    (∀ y : Fin n → ℝ, y ∈ openCube n → ¬ ContDiffAt ℝ L.length g (pt x y)) := by
  by_cases hne : ({y : Fin n → ℝ | y ∈ openCube n ∧ ContDiffAt ℝ L.length g (pt x y)}).Nonempty
  · left
    obtain ⟨y, hy, hmax⟩ := Work.WilG4c.exists_nearmax_of_bdd hne
      (fun y => iteratedFDeriv ℝ L.length g (pt x y) (fun j => Pi.single (L.get j) 1)) hBdd
    exact ⟨y, hy.1, hy.2, fun y' hy' hcd => hmax y' ⟨hy', hcd⟩⟩
  · right
    intro y hy hcd
    exact hne ⟨y, hy, hcd⟩

/-! ## 2. The `ℝ ≃ₗᵢ (Fin 1 → ℝ)` transport

`Work.WilG4a.fin1LIE : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ` is `t ↦ t 0`; its inverse is the constant map
`s ↦ fun _ => s`.  Composition with a linear isometry equivalence preserves `ContDiffAt` and the
operator norms of all iterated derivatives
(`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right`). -/

theorem fin1_symm_apply (s : ℝ) : (Work.WilG4a.fin1LIE.symm s : Fin 1 → ℝ) = fun _ => s := rfl

/-- The `ℝ`-form of `ContDiffAt` for a function of `Fin 1 → ℝ`. -/
theorem fin1_contDiffAt_at {r : ℕ} {f : (Fin 1 → ℝ) → ℝ} {x : ℝ}
    (h : ContDiffAt ℝ r f (fun _ : Fin 1 => x)) :
    ContDiffAt ℝ r (fun s : ℝ => f (fun _ => s)) x := by
  have hmap : ContDiffAt ℝ r (fun s : ℝ => (fun _ : Fin 1 => s)) x := by
    rw [contDiffAt_pi]
    intro i
    exact contDiffAt_id
  exact h.comp x hmap

/-- The `ℝ`-form of the unit operator-norm bound of `F1Affine`. -/
theorem fin1_norm_iteratedFDeriv_le {m : ℕ} {f : (Fin 1 → ℝ) → ℝ} {x : ℝ}
    (h : ‖iteratedFDeriv ℝ m f (fun _ : Fin 1 => x)‖ ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun s : ℝ => f (fun _ => s)) x‖ ≤ 1 := by
  have hcomp : (fun s : ℝ => f (fun _ => s)) = f ∘ ⇑Work.WilG4a.fin1LIE.symm := rfl
  rw [hcomp, Work.WilG4a.fin1LIE.symm.norm_iteratedFDeriv_comp_right]
  exact h

/-- The `ℝ`-form of the unit operator-norm bound of `F1Affine`, for the *composite* with an
affine chart `t ↦ α + β · t`: the conclusion of `F1Affine` for a tuple member `M` is a
statement about `fun t : Fin 1 → ℝ => M l (fun _ => α + β * t 0)`. -/
theorem fin1_norm_iteratedFDeriv_affine_le {m : ℕ} {M : (Fin 1 → ℝ) → ℝ} {α β x : ℝ}
    (h : ‖iteratedFDeriv ℝ m (fun u : Fin 1 → ℝ => M (fun _ => α + β * u 0))
            (fun _ : Fin 1 => x)‖ ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun s : ℝ => M (fun _ => α + β * s)) x‖ ≤ 1 :=
  fin1_norm_iteratedFDeriv_le (f := fun u : Fin 1 → ℝ => M (fun _ => α + β * u 0)) h

/-- The `ℝ`-form of `ContDiffAt` for the composite with an affine chart. -/
theorem fin1_contDiffAt_affine {r : ℕ} {M : (Fin 1 → ℝ) → ℝ} {α β x : ℝ}
    (h : ContDiffAt ℝ r (fun u : Fin 1 → ℝ => M (fun _ => α + β * u 0))
      (fun _ : Fin 1 => x)) :
    ContDiffAt ℝ r (fun s : ℝ => M (fun _ => α + β * s)) x :=
  fin1_contDiffAt_at h

/-! ## 3. The `hgd` producer of the engine

`Work.WilkG4c.curve_bound` asks `‖D^m (γᵢ') x‖ ≤ 1` for `m ≤ k`.  If the tuple member
`γᵢ ∘ φ` has unit jets up to order `r + 1`, then `(γᵢ ∘ φ)'` has unit jets up to order `r`,
because `‖D^m (deriv f) x‖ = ‖D^{m+1} f x‖` (`Work.WilG4c.norm_iteratedFDeriv_deriv_le`). -/
theorem hgd_of_jet {r : ℕ} (g : ℝ → ℝ) (x : ℝ)
    (h : ∀ m : ℕ, m ≤ r + 1 → ‖iteratedFDeriv ℝ m g x‖ ≤ 1) :
    ∀ m : ℕ, m ≤ r → ‖iteratedFDeriv ℝ m (deriv g) x‖ ≤ 1 := by
  intro m hm
  rw [Work.WilG4c.norm_iteratedFDeriv_deriv_le g x m]
  exact h (m + 1) (by omega)

end Work.WilkG4c
