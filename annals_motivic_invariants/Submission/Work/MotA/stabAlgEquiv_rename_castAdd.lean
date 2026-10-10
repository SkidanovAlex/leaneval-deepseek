import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotA

open MvPolynomial

def finCastAddEquiv (n k : ℕ) : Fin (n + k) ≃ Fin k ⊕ Fin n := (finSumFinEquiv (m := n) (n := k)).symm.trans (Equiv.sumComm (Fin n) (Fin k))

noncomputable def stabAlgEquiv (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ) : MvPolynomial (Fin (n + k)) 𝕜 ≃ₐ[𝕜] MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜) := (MvPolynomial.renameEquiv 𝕜 (finCastAddEquiv n k)).trans (MvPolynomial.sumAlgEquiv 𝕜 (Fin k) (Fin n))

theorem stabAlgEquiv_rename_castAdd (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ) (r : MvPolynomial (Fin n) 𝕜) : stabAlgEquiv 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) r) = MvPolynomial.C r := by
  simp only [stabAlgEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply]
  have hfun : (⇑(finCastAddEquiv n k) ∘ Fin.castAdd k) = (Sum.inr : Fin n → Fin k ⊕ Fin n) := by
    funext j; simp [finCastAddEquiv]
  have h : MvPolynomial.rename (finCastAddEquiv n k) (MvPolynomial.rename (Fin.castAdd k) r)
      = MvPolynomial.rename Sum.inr r := by
    rw [MvPolynomial.rename_rename (Fin.castAdd k) (finCastAddEquiv n k) r, hfun]
  rw [h]
  have h2 : (MvPolynomial.sumAlgEquiv 𝕜 (Fin k) (Fin n)) (MvPolynomial.rename Sum.inr r)
      = MvPolynomial.C r := by
    simpa [MvPolynomial.algebraMap_eq] using
      congrArg (fun f => f r) (MvPolynomial.sumAlgEquiv_comp_rename_inr 𝕜 (Fin k) (Fin n))
  rw [h2]

end Work.MotA
