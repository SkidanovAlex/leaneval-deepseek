/-
  WilG4a : the `ℝ`-coordinate family lemma `F1Affine1` implies the frozen
  `WilkiesDesign.CG.F1Affine` (the `Fin 1 → ℝ`-coordinate version).

  The two statements differ only in how the single variable is coded: `F1Affine1`
  uses a plain real `t : ℝ`, while `F1Affine` uses `t : Fin 1 → ℝ`.  The bridge is
  the linear isometry equivalence `fin1LIE : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ`, `t ↦ t 0`:
  it identifies the two coordinate systems, transports `ContDiffOn`, and preserves
  the norms `‖iteratedFDeriv …‖` appearing in the derivative bounds.
-/
import Mathlib
import Submission.Work.WilG4a.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture
open WilkiesDesign.CG

/-! ## The coordinate identification `Fin 1 → ℝ ≃ ℝ` -/

/-- The linear isometry equivalence `(Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ`, given by `t ↦ t 0`. -/
def fin1LIE : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := LinearEquiv.funUnique (Fin 1) ℝ ℝ
  norm_map' := by
    intro x
    rw [LinearEquiv.funUnique_apply]
    show ‖Function.eval default x‖ = ‖x‖
    rw [Pi.norm_def]
    simp

@[simp] lemma fin1LIE_apply (t : Fin 1 → ℝ) : fin1LIE t = t 0 := rfl

lemma fin1LIE_coe_clm : ⇑(fin1LIE : (Fin 1 → ℝ) →L[ℝ] ℝ) = fun t => t 0 := rfl

lemma fin1LIE_preimage_I : (⇑(fin1LIE : (Fin 1 → ℝ) →L[ℝ] ℝ)) ⁻¹' I = openCube 1 := by
  ext t
  simp only [Set.mem_preimage, openCube, Set.mem_ofPred_eq, Set.mem_Ioo, I, fin1LIE_coe_clm,
    Fin.forall_fin_one]

/-- The `m`-th derivative norm of `g ∘ fin1LIE` is the absolute `m`-th derivative of `g`. -/
lemma norm_iteratedFDeriv_comp_fin1LIE (g : ℝ → ℝ) (m : ℕ) (t : Fin 1 → ℝ) :
    ‖iteratedFDeriv ℝ m (g ∘ ⇑fin1LIE) t‖ = |iteratedDeriv m g (t 0)| := by
  rw [fin1LIE.norm_iteratedFDeriv_comp_right, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, fin1LIE_apply]

/-- `ContDiffOn` transfers through `fin1LIE`. -/
lemma contDiffOn_comp_fin1LIE {g : ℝ → ℝ} {r : ℕ} (hg : ContDiffOn ℝ r g I) :
    ContDiffOn ℝ r (g ∘ ⇑fin1LIE) (openCube 1) := by
  have h := ContDiffOn.comp_continuousLinearMap (𝕜 := ℝ) hg (fin1LIE : (Fin 1 → ℝ) →L[ℝ] ℝ)
  rwa [fin1LIE_preimage_I] at h

/-! ## The graph of a one-variable family in the two coordinate systems -/

/-- The graph of a family of one-variable functions, read in `ℝ`-coordinates
(`graphFam`) or in `Fin 1 → ℝ`-coordinates (`famGraph`), agree. -/
lemma graphFam_eq_famGraph {p : ℕ} (F : (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    graphFam (fun l x => F l (fun _ => x)) = famGraph F := by
  have hfun : (fun z : Fin (p + 1) → ℝ => F (fun i => z (Fin.castSucc i)) (fun _ => z (Fin.last p)))
      = (fun z : Fin (p + 1) → ℝ =>
          F (fun j => z (Fin.castAdd 1 j)) (fun j : Fin 1 => z (Fin.natAdd p j))) := by
    funext z
    rw [show (fun i : Fin p => z (Fin.castSucc i)) = (fun j : Fin p => z (Fin.castAdd 1 j)) from by
          funext j; rw [show Fin.castSucc j = Fin.castAdd 1 j from Fin.ext rfl],
        show (fun _ : Fin 1 => z (Fin.last p)) = (fun j : Fin 1 => z (Fin.natAdd p j)) from by
          funext j; have h : j = 0 := Subsingleton.elim j 0; rw [h]; simp [Fin.natAdd, Fin.last]]
  simp only [graphFam, famGraph]
  rw [hfun]

/-! ## The transfer -/

theorem f1affine_of_f1affine1 (S : WilkiesDesign.SOMin) (p : ℕ)
    (h : Work.WilG4a.F1Affine1 S p) : WilkiesDesign.CG.F1Affine S p := by
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
    obtain ⟨hg1, hg2, hl⟩ := hchart αβ hαβ
    refine ⟨hg1, hg2, ?_⟩
    intro l hlΛ
    obtain ⟨hβ, hα, hsum, hcond⟩ := hl l hlΛ
    refine ⟨hβ, hα, hsum, ?_⟩
    intro i
    obtain ⟨hcd, hbnd⟩ := hcond i
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
