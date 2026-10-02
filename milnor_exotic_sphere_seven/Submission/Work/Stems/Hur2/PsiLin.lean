import Submission.Work.Stems.Hur2.PsiHomotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Ψ` as a `ℤ`-linear map on 2-chains

Hutchings' `Ψ` is the `ℤ`-linear extension of the cube-wise filling `psiGenLoop`: a 2-chain
`Σ nᵢ σᵢ` goes to `Σ nᵢ Ψ(σᵢ)`, an element of the abelian group `π₂(X,x₀)`.  The three properties
the Hurewicz argument needs are then statements about this single map:

* **(Z)** `PsiLin x₀ (single p.1 1) = ⟦p⟧` for every *based* cube `p` (`PsiLin_single_based`);
* **(Y)** `PsiLin x₀ (cubD 2 X (single τ 1)) = 0` for every 3-cube `τ` (`PsiLin_cubD_single`);
* **(i)** `PsiLin x₀ (single c 1) = 0` for every *degenerate* 2-cube `c` (`PsiLin_single_degenerate`).

Given the three, `[p] = Ψ(p) = Ψ(∂d) + Ψ(deg) = 0 + 0 = 0` as soon as the bridge produces
`p = ∂d + deg` (the cubical chain of `p`, up to a degenerate 2-chain).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- **`Ψ` as a `ℤ`-linear map on the cubical 2-chains.** -/
def PsiLin (x₀ : X) : Cub 2 X →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x₀) :=
  Finsupp.linearCombination ℤ fun c : C(IC 2, X) => Additive.ofMul ⟦psiGenLoop x₀ c⟧

@[simp]
theorem PsiLin_single (x₀ : X) (c : C(IC 2, X)) :
    PsiLin x₀ (Finsupp.single c 1) = Additive.ofMul ⟦psiGenLoop x₀ c⟧ := by
  rw [PsiLin, Finsupp.linearCombination_single, one_smul]
  rfl

/-- **(Z) in chain form.** -/
theorem PsiLin_single_based (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    PsiLin x₀ (Finsupp.single p.1 1) = Additive.ofMul ⟦p⟧ := by
  rw [PsiLin_single]
  exact congrArg Additive.ofMul (Quotient.sound (homotopic_psiGenLoop x₀ p)).symm

end

end Work.Stems.Hur2
