import Mathlib
import Submission.Work.CFT.ClassFormation.Defs

/-!
# Auxiliary definitions for the field duality of group (co)homology

We collect the vocabulary used by the proof that, for a finite group `G` and a field `k`,
the `k`-dimension of `Hⁿ(G, k)` equals that of `Hₙ(G, k)` (trivial coefficients): the
canonical `k`-linear duality `(α → k) ≃ₗ[k] (α →₀ k) →ₗ[k] k`, the two inhomogeneous
(co)chain complexes of the trivial representation, and their differentials.
-/

open CategoryTheory

namespace Work.CFT.ClassFormation.Schur

noncomputable section

variable (k : Type) [Field k] (G : Type) [Group G] [Fintype G]

/-- The trivial `k`-linear `G`-representation on `k`. -/
abbrev trivRep : Rep k G := Rep.trivial k G k

/-- The canonical `k`-linear equivalence `(α → k) ≃ₗ[k] (α →₀ k) →ₗ[k] k` sending a function
`f` to the linear functional `x ↦ ∑ₐ xₐ · f a`.  It is the universal property of the free
module `α →₀ k`. -/
def psi (α : Type*) : (α → k) ≃ₗ[k] ((α →₀ k) →ₗ[k] k) :=
  Finsupp.llift k k k α

@[simp] lemma psi_single (α : Type*) (f : α → k) (a : α) (b : k) :
    psi k α f (Finsupp.single a b) = b * f a := by
  simp [psi, Finsupp.llift]

/-- The complex of inhomogeneous chains over the trivial `k`-representation of `G`. -/
abbrev chainCx : ChainComplex (ModuleCat k) ℕ :=
  groupHomology.inhomogeneousChains (trivRep k G)

/-- The complex of inhomogeneous cochains over the trivial `k`-representation of `G`. -/
abbrev cochainCx : CochainComplex (ModuleCat k) ℕ :=
  groupCohomology.inhomogeneousCochains (trivRep k G)

/-- The chain differential `C (n+1) → C n` of the inhomogeneous chains. -/
abbrev dCh (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] ((Fin n → G) →₀ k) :=
  (groupHomology.inhomogeneousChains.d (trivRep k G) n).hom

/-- The cochain differential `C n → C (n+1)` of the inhomogeneous cochains. -/
abbrev dCo (n : ℕ) : ((Fin n → G) → k) →ₗ[k] ((Fin (n + 1) → G) → k) :=
  (inhomogeneousCochains.d (trivRep k G) n).hom

omit [Fintype G] in
/-- **The cochain differential is the transpose of the chain differential.**  Under the
canonical duality `psi`, the cochain differential `Cⁿ → Cⁿ⁺¹` of the inhomogeneous cochains is
the transpose of the chain differential `Cₙ₊₁ → Cₙ` of the inhomogeneous chains. -/
lemma psi_dCo (n : ℕ) (f : (Fin n → G) → k) :
    psi k (Fin (n + 1) → G) (dCo k G n f) =
      (dCh k G n).dualMap (psi k (Fin n → G) f) := by
  apply Finsupp.lhom_ext
  intro g b
  rw [psi_single, LinearMap.dualMap_apply]
  rw [dCo, inhomogeneousCochains.d_hom_apply, dCh, groupHomology.inhomogeneousChains.d_single]
  simp only [Representation.isTrivial_apply, map_add, map_sum, map_smul, psi_single]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- The `ComplexShape.down ℕ` predecessor of `n` is `n + 1`. -/
lemma down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 := by
  rw [ComplexShape.prev_eq' (h := ?_)]; simp [ComplexShape.down]

/-- The `ComplexShape.down ℕ` successor of `n` is `n - 1`. -/
lemma down_next (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [ComplexShape.next_eq_self']; intro k hk; simp [ComplexShape.down] at hk
  · rw [ComplexShape.next_eq' (h := ?_)]; simp only [ComplexShape.down, ComplexShape.down']; omega

/-- The `ComplexShape.up ℕ` predecessor of `n` is `n - 1`. -/
lemma up_prev (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [ComplexShape.prev_eq_self']; intro k hk; simp [ComplexShape.up] at hk
  · rw [ComplexShape.prev_eq' (h := ?_)]; simp only [ComplexShape.up, ComplexShape.up']; omega

/-- The `ComplexShape.up ℕ` successor of `n` is `n + 1`. -/
lemma up_next (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 := by
  rw [ComplexShape.next_eq' (h := ?_)]; simp [ComplexShape.up]

/-- If `g ∘ f = 0` then the transpose of `f` lies in the kernel of the transpose of `g`. -/
lemma dualMap_comp_dualMap_eq_zero {R : Type} [CommSemiring R]
    {M₁ M₂ M₃ : Type} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [AddCommMonoid M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : g.comp f = 0) :
    f.dualMap.comp g.dualMap = 0 := by
  rw [LinearMap.dualMap_comp_dualMap, h]; ext x; simp [LinearMap.dualMap_apply]

end

end Work.CFT.ClassFormation.Schur
