import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.LamAS.asML
import Submission.Work.MotC5N3.LamAS.algClosure_algHom_surjective

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.LamAS
/-- Every `K`-algebra automorphism of the two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯` extends to a `K`-algebra automorphism of the algebraic closure `Work.MotC5N3.KbA K` (by the standard extension of embeddings of algebraic extensions into an algebraically closed field). -/
theorem asExtension (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (f₁ f₂ : K)
    (γ : ↥(Work.MotC5N3.LamAS.asL2 f₁ f₂) ≃ₐ[K]
      ↥(Work.MotC5N3.LamAS.asL2 f₁ f₂)) :
    ∃ γb : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K,
      ∀ l : ↥(Work.MotC5N3.LamAS.asL2 f₁ f₂),
        γb (l : Work.MotC5N3.KbA K) = (γ l : Work.MotC5N3.KbA K) := by
  -- `L = K⟮asRoot f₁, asRoot f₂⟯` is the intermediate field to be embedded.
  let L := ↥(Work.MotC5N3.LamAS.asL2 f₁ f₂)
  -- The `K`-embedding `L → Work.MotC5N3.KbA K` induced by `γ`.
  let f : L →ₐ[K] Work.MotC5N3.KbA K :=
    (IsScalarTower.toAlgHom (K) L (Work.MotC5N3.KbA K)).comp γ.toAlgHom
  -- `Work.MotC5N3.KbA K` is algebraic over `L` (it is algebraic over `K`) and algebraically closed
  -- and `K`-algebraically closed, so the embedding `f` extends to `Work.MotC5N3.KbA K →ₐ[K] Work.MotC5N3.KbA K`.
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := K)
    (L := L) (E := Work.MotC5N3.KbA K) (M := Work.MotC5N3.KbA K) f
  have hφ' : ∀ l : L, φ (l : Work.MotC5N3.KbA K) = (γ l : Work.MotC5N3.KbA K) := by
    intro l
    have h := DFunLike.congr_fun hφ l
    have e1 : (AlgHom.domRestrict L φ) l = φ (l : Work.MotC5N3.KbA K) := rfl
    have e2 : f l = (γ l : Work.MotC5N3.KbA K) := rfl
    rw [e1, e2] at h
    exact h
  -- An injective `𝕜`-algebra endomorphism of `Work.MotC5N3.KbA K = \overline{𝕜(t)}` is surjective.
  exact ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), hφ'⟩

end Work.MotC5N3.LamAS