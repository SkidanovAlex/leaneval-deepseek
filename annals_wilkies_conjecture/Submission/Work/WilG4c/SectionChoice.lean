import Mathlib
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.ThetaGraphMem
import Submission.Work.WilG4c.CoordGraphMem

/-!
# Section choice with sharp bounds

The G4c area consumes BNZ's definable choice `ChoiceHyp S` (the hole `CG.G1_choice`) in the
following form: given a map `θ : ℝ^q → ℝ^p` all of whose coordinate graphs are `Ω`-sets of a
common format/degree, there is a section `μ : ℝ^p → ℝ^q` of `θ` (over the image of `θ`) whose
coordinate graphs are again `Ω`-sets, with a format `a` depending only on `(p,q,F2)` and a
degree `b.eval D` polynomial in the degree `D` of the hypothesis.

The proof is a single application of `ChoiceHyp` to the graph of `θ`:

* `Work.WilG4c.ThetaGraphMem` (delegated) — the graph of `θ`
  `{z : ℝ^{p+q} | ∀ j : Fin p, z (castAdd q j) = θ (fun i => z (natAdd p i)) j}` (the `p`
  values `= θ y` first, the argument `y` last, matching `ChoiceHyp`'s `Fin.append l y`) is an
  `Ω`-set, because it is the intersection over `j` of the pullbacks
  `coordPre ι_j (graphOf θ_j)`;
* `ChoiceHyp` then produces a section `f : ℝ^p → ℝ^q` together with the `Ω`-membership of its
  joint graph `G = {z | ∀ j, z_{p+j} = f(z_{<p})_j}`;
* the section property `θ (f l) = l` is the one place where the shapes are used: `Fin.append l y`
  is the point of the graph of `θ` over `θ y`;
* `Work.WilG4c.CoordGraphMem` (delegated) — the `j`-th coordinate graph of a section is the
  image of its joint graph under the coordinate map `ι'_j`, whence `Ω`-membership by
  `Work.WilG5.coordImage_mem`.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG4c

open WilkiesDesign

theorem SectionChoice (S : WilkiesDesign.SOMin) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (p q F2 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)),
      (∀ j : Fin p, WilkiesDesign.graphOf (fun μ : Fin q → ℝ => θ μ j) ∈ S.Ω F2 D (q + 1)) →
      ∃ μ : (Fin p → ℝ) → (Fin q → ℝ),
        (∀ l : Fin p → ℝ, (∃ μ₀ : Fin q → ℝ, θ μ₀ = l) → θ (μ l) = l) ∧
        (∀ j : Fin q, WilkiesDesign.graphOf (fun l : Fin p → ℝ => μ l j) ∈
          S.Ω a (b.eval D) (p + 1)) := by
  obtain ⟨FX, bX, hTheta⟩ := ThetaGraphMem S p q F2
  obtain ⟨a', b', hChoice⟩ := hchoice FX p q
  obtain ⟨A, B, hCoord⟩ := CoordGraphMem S p q
  refine ⟨a' + A, (b' + B).comp bX, ?_⟩
  intro D θ hθ
  obtain ⟨f, hsel, hG⟩ := hChoice (bX.eval D)
    ({z : Fin (p + q) → ℝ | ∀ j : Fin p,
      z (Fin.castAdd q j) = θ (fun i : Fin q => z (Fin.natAdd p i)) j})
    (hTheta D θ hθ)
  refine ⟨f, ?_, ?_⟩
  · intro l hl
    obtain ⟨μ₀, hμ₀⟩ := hl
    -- `Fin.append l μ₀` is the point of the graph of `θ` over `θ μ₀ = l`
    have hy : Fin.append l μ₀ ∈ {z : Fin (p + q) → ℝ | ∀ j : Fin p,
        z (Fin.castAdd q j) = θ (fun i : Fin q => z (Fin.natAdd p i)) j} := by
      intro j
      have h2 : (fun i : Fin q => (Fin.append l μ₀) (Fin.natAdd p i)) = μ₀ := by
        funext i; exact Fin.append_right ..
      rw [Fin.append_left, h2]
      exact congrFun hμ₀.symm j
    have h1 := hsel l ⟨μ₀, hy⟩
    funext j
    have hj := h1 j
    have hf : (fun i : Fin q => (Fin.append l (f l)) (Fin.natAdd p i)) = f l := by
      funext i; exact Fin.append_right ..
    rw [Fin.append_left, hf] at hj
    exact hj.symm
  · intro j
    simpa only [Polynomial.eval_comp] using hCoord (bX.eval D) a' b' f hG j

end Work.WilG4c
