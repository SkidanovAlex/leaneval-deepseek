import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.MotAS

/-- Auxiliary: if a polynomial `q` over a field `K` is invariant under the substitutions
`X ↦ X + 1` and `X ↦ X - 1`, then `AdjoinRoot q` carries a `K`-algebra automorphism
sending `root q` to `root q + 1`. -/
theorem adjoinRoot_exists_aut_shift {K : Type} [Field K] (q : Polynomial K)
    (h1 : q.comp (Polynomial.X + 1) = q) (hm1 : q.comp (Polynomial.X - 1) = q) :
    ∃ σ : AdjoinRoot q ≃ₐ[K] AdjoinRoot q,
      σ (AdjoinRoot.root q) = AdjoinRoot.root q + 1 := by
  have hr : Polynomial.aeval (AdjoinRoot.root q) q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hof1 : Polynomial.eval₂ (AdjoinRoot.of q) (AdjoinRoot.root q + 1) q = 0 := by
    have h2 := Polynomial.aeval_comp (p := q) (q := Polynomial.X + 1) (x := AdjoinRoot.root q)
    rw [h1, hr] at h2
    simp only [Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_one] at h2
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq] at h2
    exact h2.symm
  have hofm : Polynomial.eval₂ (AdjoinRoot.of q) (AdjoinRoot.root q - 1) q = 0 := by
    have h2 := Polynomial.aeval_comp (p := q) (q := Polynomial.X - 1) (x := AdjoinRoot.root q)
    rw [hm1, hr] at h2
    simp only [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_one] at h2
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq] at h2
    exact h2.symm
  let σ : AdjoinRoot q →ₐ[K] AdjoinRoot q :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId K (AdjoinRoot q)) (AdjoinRoot.root q + 1)
      (by simpa only [Algebra.toRingHom_ofId, AdjoinRoot.algebraMap_eq] using hof1)
  let τ : AdjoinRoot q →ₐ[K] AdjoinRoot q :=
    AdjoinRoot.liftAlgHom q (Algebra.ofId K (AdjoinRoot q)) (AdjoinRoot.root q - 1)
      (by simpa only [Algebra.toRingHom_ofId, AdjoinRoot.algebraMap_eq] using hofm)
  have hσ : σ (AdjoinRoot.root q) = AdjoinRoot.root q + 1 := by simp [σ]
  have hτ : τ (AdjoinRoot.root q) = AdjoinRoot.root q - 1 := by simp [τ]
  have h₁ : σ.comp τ = AlgHom.id K (AdjoinRoot q) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply]
    simp [hσ, hτ, AlgHom.id_apply]
  have h₂ : τ.comp σ = AlgHom.id K (AdjoinRoot q) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply]
    simp [hσ, hτ, AlgHom.id_apply]
  exact ⟨AlgEquiv.ofAlgHom σ τ h₁ h₂, hσ⟩

theorem ASZB0ASAut (K : Type) [Field K] [CharP K 5] (g : K)
    (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∃ σ : AdjoinRoot (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ≃ₐ[K]
        AdjoinRoot (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g),
      σ (AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)) =
        AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K).comp
        (Polynomial.X + 1)
      = Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g := by
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [add_pow_char, one_pow]
    first | refl_ring1 | ring
  have hm1 : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial K).comp
        (Polynomial.X - 1)
      = Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g := by
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [sub_pow_char, one_pow]
    first | refl_ring1 | ring
  exact adjoinRoot_exists_aut_shift (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) h1 hm1

end Work.MotAS
