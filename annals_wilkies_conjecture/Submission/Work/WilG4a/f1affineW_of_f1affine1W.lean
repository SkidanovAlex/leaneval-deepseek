/-
  WilG4a : the `ℝ`-coordinate corrected lemma `F1Affine1W` implies the `Fin 1 → ℝ`-coordinate
  corrected lemma `F1AffineW`.

  This is the `W`-analogue of `f1affine_of_f1affine1`: the two statements differ only in how
  the single variable is coded (`ℝ` versus `Fin 1 → ℝ`), and the per-chart condition carries
  the extra conjunct `∀ t ∈ I, αβ.1 l + αβ.2 l * t ∈ I`.  The bridge is again the linear
  isometry equivalence `fin1LIE : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ`, `t ↦ t 0`, which transports
  `ContDiffOn` and preserves the derivative norms `‖iteratedFDeriv …‖`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.F1Affine1W
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4a.f1affine_of_f1affine1

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture
open WilkiesDesign.CG

theorem f1affineW_of_f1affine1W (S : WilkiesDesign.SOMin) (p : ℕ) (h : Work.WilG4a.F1Affine1W S p) : Work.WilG4a.F1AffineW S p := by
  intro F0
  obtain ⟨a, b, c, hc⟩ := h F0
  refine ⟨a, b, c, ?_⟩
  intro D r k ε hε0 hε1 Λ F hgraph hI
  -- Recode the `Fin 1 → ℝ`-valued family as a real-valued family.
  let F' : Fin k → (Fin p → ℝ) → ℝ → ℝ := fun i l x => F i l (fun _ => x)
  have hgraph' : ∀ i, graphFam (F' i) ∈ S.Ω F0 D (p + 1 + 1) := by
    intro i
    have h1 : graphFam (F' i) = famGraph (F i) := graphFam_eq_famGraph (F i)
    rw [h1]
    exact hgraph i
  have hI' : ∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F' i l x ∈ I := by
    intro i l hl x hx
    exact hI i l hl (fun _ => x) (by intro j; exact hx)
  obtain ⟨Φ, hcard, hchart, hcover⟩ := hc D r k ε hε0 hε1 Λ F' hgraph' hI'
  refine ⟨Φ, hcard, ?_, ?_⟩
  · intro αβ hαβ
    obtain ⟨hg1, hg2, hll⟩ := hchart αβ hαβ
    refine ⟨hg1, hg2, ?_⟩
    intro l hlΛ
    obtain ⟨hβ, hα, hsum, hcond, hrest⟩ := hll l hlΛ
    refine ⟨hβ, hα, hsum, hcond, ?_⟩
    intro i
    obtain ⟨hcd, hbnd⟩ := hrest i
    refine ⟨?_, ?_⟩
    · -- smoothness along the affine chart
      exact contDiffOn_comp_fin1LIE hcd
    · -- derivative bound along the affine chart
      intro m hm t ht
      have ht0 : t 0 ∈ I := ht 0
      have hb := hbnd m hm (t 0) ht0
      calc ‖iteratedFDeriv ℝ m (fun s : Fin 1 → ℝ => F i l (fun _ => αβ.1 l + αβ.2 l * s 0)) t‖
          = ‖iteratedFDeriv ℝ m
              ((fun s : ℝ => F' i l (αβ.1 l + αβ.2 l * s)) ∘ ⇑fin1LIE) t‖ := rfl
        _ = |iteratedDeriv m (fun s : ℝ => F' i l (αβ.1 l + αβ.2 l * s)) (t 0)| :=
              norm_iteratedFDeriv_comp_fin1LIE _ m t
        _ ≤ 1 := hb
  · intro l hlΛ x hx
    -- the covering condition is literally the same statement in both definitions
    exact hcover l hlΛ x hx

end Work.WilG4a
