import Mathlib
import Submission.Work.HP.MDEstimates.cubLevelForms
import Submission.Work.Q44Geom.uniqueDirection

namespace Work.HP.MDEstimates

open Work.Q44Geom

/-- The point `substPoint w b₁ b₂ x u` is the sum of `toV w x` and the line combination
`u 0 • b₁ + u 1 • b₂`. -/
lemma substPoint_eq_toV_add (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (x : Fin 3 → ℚ)
    (u : Fin 2 → ℚ) :
    Work.Q44Geom.substPoint w b₁ b₂ x u
      = Work.Q44Geom.toV w x + (u 0 • b₁ + u 1 • b₂) := by
  funext i
  simp only [Work.Q44Geom.substPoint, Pi.add_apply, Pi.smul_apply,
    Work.Q44Geom.toV_apply, Finset.sum_apply]
  have hs : (∑ a : Fin 3, x a * w a i) = ∑ a : Fin 3, w a i * x a :=
    Finset.sum_congr rfl fun a _ => mul_comm (x a) (w a i)
  rw [hs]
  ring_nf

theorem cubPlaneDirection (b₁ b₂ : Fin 5 → ℚ) (w : Fin 3 → Fin 5 → ℚ)
    (hb : LinearIndependent ℚ (Fin.append w ![b₁, b₂]))
    (hsp : Submodule.span ℚ (Set.range (Fin.append w ![b₁, b₂])) = ⊤)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) B = 0)
    (P : Submodule ℚ (Fin 5 → ℚ)) (hb1 : b₁ ∈ P) (hb2 : b₂ ∈ P)
    (hr : Module.finrank ℚ P = 3) (hvanish : ∀ x ∈ P, MvPolynomial.eval x B = 0) :
    ∃ L : Submodule ℚ (Fin 3 → ℚ), Module.finrank ℚ L = 1 ∧
      P = Submodule.span ℚ ({b₁, b₂} ∪ Set.range (fun p : L => Work.Q44Geom.toV w (p : Fin 3 → ℚ))) ∧
      (∀ x ∈ L, ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range 3, i + j ≤ 2 →
        MvPolynomial.eval x (Work.Q44Geom.levelForm w b₁ b₂ B ![i, j]) = 0) := by
  classical
  obtain ⟨L, hLp, -⟩ := Work.Q44Geom.uniqueDirection b₁ b₂ w hb hsp P hb1 hb2 hr
  refine ⟨L, hLp.1, hLp.2, ?_⟩
  intro x hx i hi j hj hij
  have hmem : Work.Q44Geom.toV w x ∈ P := by
    rw [hLp.2]
    exact Submodule.subset_span (Or.inr ⟨⟨x, hx⟩, rfl⟩)
  have hsub : ∀ u : Fin 2 → ℚ,
      MvPolynomial.eval (Work.Q44Geom.substPoint w b₁ b₂ x u) B = 0 := by
    intro u
    rw [substPoint_eq_toV_add w b₁ b₂ x u]
    exact hvanish _ (P.add_mem hmem (P.add_mem (P.smul_mem (u 0) hb1) (P.smul_mem (u 1) hb2)))
  exact (isSolIffCub w b₁ b₂ B hB hℓ x).1 hsub i hi j hj hij

end Work.HP.MDEstimates
