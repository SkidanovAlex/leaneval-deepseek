/-
  WilG4c / famGraph_pullX — pulling a family back along the affine `x`-chart
  `x = α(l) + β(l)·t₀`.

  Given `famGraph f ∈ S.Ω F0 D (p + (n+1) + 1)` for a family `f` over the parameter space
  `ℝ^p`, together with `Ω`-graphs for the two coefficient functions `α, β : ℝ^p → ℝ`, the
  graph of the pulled-back family

      `fun l t => f l (pt (α l + β l * t 0) (Fin.tail t))`

  is `Ω`-bounded with format `F0 + Fa + K` and degree `D + 2 * Da + K`, for a constant `K`
  depending only on `S`, `p` and `n`.

  The proof is a per-coordinate composition (`Work.WilkG4c.graphOf_comp_deg`) of the flattened
  family `flatFun f` with the chart `flatChart χ`, whose coordinates are
  `χ 0 = fun l t => α l + β l * t 0` (the only expensive one, handled by
  `Work.WilkG4c.famGraph_linX`: format `+Fa`, degree `+2*Da`) and `χ (k+1) = fun l t => t (k+1)`
  (a plain coordinate projection, format and degree `O(p + n)`).
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.graphOf_comp_deg
import Submission.Work.WilG4c.famGraph_linX

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1
open scoped BigOperators

theorem famGraph_pullX (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K : ℕ, ∀ (Fa Da F0 D : ℕ) (α β : (Fin p → ℝ) → ℝ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.graphOf α ∈ S.Ω Fa Da (p + 1) →
      WilkiesDesign.graphOf β ∈ S.Ω Fa Da (p + 1) →
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      WilkiesDesign.CG.famGraph
        (fun l t => f l (Work.WilkG4c.pt (α l + β l * t 0) (Fin.tail t)))
        ∈ S.Ω (F0 + Fa + K) (D + 2 * Da + K) (p + (n + 1) + 1) := by
  obtain ⟨C₁, C₂, hcomp⟩ := Work.WilG4c.graphOf_comp_deg S (p + (n + 1))
  obtain ⟨K', hlin⟩ := Work.WilG4c.famGraph_linX S p n
  refine ⟨K' + C₁ + C₂ + p * (p + (n + 1) + 1) + n * (p + (n + 1) + 1) + p + n + 1, ?_⟩
  intro Fa Da F0 D α β f hα hβ hf
  -- the chart: the `x`-coordinate is `α l + β l * t 0`, the other coordinates pass through
  let χ : Fin (n + 1) → (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ :=
    Fin.cases (fun l t => α l + β l * t 0) (fun k l t => t k.succ)
  -- per-coordinate formats / degrees of the chart
  let F₂ : Fin (p + (n + 1)) → ℕ := Fin.addCases
    (fun _ : Fin p => p + (n + 1) + 1)
    (fun k : Fin (n + 1) => if k = 0 then Fa + K' else p + (n + 1) + 1)
  let D₂ : Fin (p + (n + 1)) → ℕ := Fin.addCases
    (fun _ : Fin p => 1)
    (fun k : Fin (n + 1) => if k = 0 then 2 * Da + K' else 1)
  have hg : WilkiesDesign.graphOf (Work.WilkG4c.flatFun f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    rwa [Work.WilkG4c.famGraph_eq_graphOf_flatFun] at hf
  have hχ0 : χ 0 = (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => α l + β l * t 0) := rfl
  have hχs : ∀ k' : Fin n,
      χ k'.succ = (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t k'.succ) := fun k' => rfl
  -- each coordinate of the chart has an `Ω`-bounded graph
  have hφ : ∀ j : Fin (p + (n + 1)),
      WilkiesDesign.graphOf (fun x : Fin (p + (n + 1)) → ℝ => Work.WilkG4c.flatChart χ x j)
        ∈ S.Ω (F₂ j) (D₂ j) (p + (n + 1) + 1) := by
    intro j
    induction j using Fin.addCases with
    | left i =>
      -- a parameter coordinate is untouched
      rw [Work.WilkG4c.graphOf_flatChart_castAdd]
      refine Omega.mono (Work.WilkG4c.graphOf_coord_mem S (Fin.castAdd (n + 1) i)) ?_ ?_
      · simp [F₂, Fin.addCases_left]
      · simp [D₂, Fin.addCases_left]
    | right k =>
      rw [Work.WilkG4c.graphOf_flatChart_natAdd]
      induction k using Fin.cases with
      | zero =>
        -- the `x`-coordinate `α l + β l * t 0`
        rw [hχ0]
        refine Omega.mono (hlin Fa Da α β hα hβ) ?_ ?_
        · simp [F₂, Fin.addCases_right]
        · simp [D₂, Fin.addCases_right]
      | succ k' =>
        -- a free coordinate `t (k'+1)`
        rw [hχs k', Work.WilkG4c.famGraph_eq_graphOf_flatFun]
        have heq : WilkiesDesign.graphOf (Work.WilkG4c.flatFun
              (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => t k'.succ))
            = WilkiesDesign.graphOf (fun x : Fin (p + (n + 1)) → ℝ => x (Fin.natAdd p k'.succ)) := by
          congr 1
        rw [heq]
        refine Omega.mono (Work.WilkG4c.graphOf_coord_mem S (Fin.natAdd p k'.succ)) ?_ ?_
        · simp [F₂, Fin.addCases_right, Fin.succ_ne_zero]
        · simp [D₂, Fin.addCases_right, Fin.succ_ne_zero]
  have hmain := hcomp F0 D F₂ D₂ (Work.WilkG4c.flatFun f) (Work.WilkG4c.flatChart χ) hg hφ
  -- the two sums of the per-coordinate bounds
  have hsumF : (∑ j : Fin (p + (n + 1)), F₂ j)
      = p * (p + (n + 1) + 1) + (Fa + K') + n * (p + (n + 1) + 1) := by
    simp only [F₂]
    rw [Fin.sum_univ_add, Fin.sum_univ_succ]
    simp only [Fin.addCases_left, Fin.addCases_right]
    simp [Fin.succ_ne_zero, Finset.sum_const, Finset.card_univ] <;> omega
  have hsumD : (∑ j : Fin (p + (n + 1)), D₂ j)
      = p * 1 + (2 * Da + K') + n * 1 := by
    simp only [D₂]
    rw [Fin.sum_univ_add, Fin.sum_univ_succ]
    simp only [Fin.addCases_left, Fin.addCases_right]
    simp [Fin.succ_ne_zero, Finset.sum_const, Finset.card_univ] <;> omega
  -- the composite is exactly the pulled-back family
  have hfun : (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => f l (fun j => χ j l t))
      = (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) =>
          f l (Work.WilkG4c.pt (α l + β l * t 0) (Fin.tail t))) := by
    funext l t
    congr 1
    funext j
    induction j using Fin.cases with
    | zero => simp [χ, Work.WilkG4c.pt_zero]
    | succ k => simp [χ, Work.WilkG4c.pt_succ, Fin.tail]
  have heq : WilkiesDesign.graphOf (Work.WilkG4c.flatFun f ∘ Work.WilkG4c.flatChart χ)
      = WilkiesDesign.CG.famGraph
          (fun l t => f l (Work.WilkG4c.pt (α l + β l * t 0) (Fin.tail t))) := by
    rw [← Work.WilkG4c.flatFun_comp χ f, Work.WilkG4c.famGraph_eq_graphOf_flatFun, hfun]
  rw [heq] at hmain
  refine Omega.mono hmain ?_ ?_
  · rw [hsumF]; omega
  · rw [hsumD]; omega

end Work.WilG4c
