import Mathlib
import Submission.Work.ORFinal.FiniteFree.ringCoherent_of_finite_free
import Submission.Work.ORReductions.Coherent.coherent_of_subfield

/-!
# Finite free monoid algebras

Let `K₀ → K` be a finite free extension of commutative rings (e.g. a finite field extension) and let
`X` be a group.  Then `K[X]` is a finite free `K₀[X]`-module, with the module structure in which
`a • m = a * m` for `a ∈ K₀[X]` acting through `mapRingHom X (algebraMap K₀ K)`.

Concretely, if `b` is a `K₀`-basis of `K` indexed by `Fin n`, then
`i ↦ MonoidAlgebra.single 1 (b i)` is a `K₀[X]`-basis of `K[X]`: the elements `single 1 (b i)`
generate everything over `K₀[X]` (because `single g k = (single g 1) * single 1 k`), and they are
independent since the `g`-coefficient of `a • single 1 (b i)` is `(a.coeff g) • b i`, so
independence reduces to independence of the `b i` over `K₀`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ORFinal.FiniteFree

theorem module_finite_free_monoidAlgebra (K₀ : Type*) [Field K₀] (K : Type*) [Field K]
    [Algebra K₀ K] [Module.Free K₀ K] [Module.Finite K₀ K] (X : Type*) [Group X]
    [J : Module (MonoidAlgebra K₀ X) (MonoidAlgebra K X)]
    (hJ : ∀ (a : MonoidAlgebra K₀ X) (m : MonoidAlgebra K X),
      a • m = MonoidAlgebra.mapRingHom X (algebraMap K₀ K) a * m) :
    Module.Free (MonoidAlgebra K₀ X) (MonoidAlgebra K X) ∧
      Module.Finite (MonoidAlgebra K₀ X) (MonoidAlgebra K X) := by
  classical
  -- A `K₀`-basis of `K`.
  let b : Module.Basis (Fin (Module.finrank K₀ K)) K₀ K := Module.finBasis K₀ K
  -- The candidate `K₀[X]`-basis of `K[X]`.
  let β : Fin (Module.finrank K₀ K) → MonoidAlgebra K X :=
    fun i => MonoidAlgebra.single (1 : X) (b i)
  -- The `g`-th coefficient of `a • single 1 (b i)` is `(a.coeff g) • b i`.
  have key : ∀ (s : MonoidAlgebra K₀ X) (i : Fin (Module.finrank K₀ K)) (g : X),
      (s • β i).coeff g = (s.coeff g) • b i := by
    intro s i g
    rw [hJ]
    simp only [β]
    rw [MonoidAlgebra.coeff_mul_single_one, MonoidAlgebra.coeff_mapRingHom,
      Algebra.smul_def]
  -- Independence, by extracting `g`-coefficients and using independence of `b`.
  have hli : LinearIndependent (MonoidAlgebra K₀ X) β := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    ext g
    have hg := congrArg (fun x : MonoidAlgebra K X => x.coeff g) hsum
    have hg' : ∑ j ∈ s, ((c j).coeff g) • b j = 0 := by
      simpa [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, key,
        MonoidAlgebra.coeff_zero] using hg
    exact (linearIndependent_iff'.mp b.linearIndependent s (fun j => (c j).coeff g) hg' i hi)
  -- `single 1 k` is a `K₀[X]`-linear combination of the `β i`.
  have hc : ∀ k : K, (MonoidAlgebra.single (1 : X) k : MonoidAlgebra K X)
      = ∑ i, (MonoidAlgebra.single (1 : X) ((b.repr k) i) : MonoidAlgebra K₀ X) • β i := by
    intro k
    ext h
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [key]
    by_cases hh : h = 1
    · subst hh
      simp [b.sum_repr]
    · simp [Ne.symm hh]
  -- Every `single g k` lies in the span of `β`.
  have key2 : ∀ (g : X) (k : K),
      (MonoidAlgebra.single g k : MonoidAlgebra K X)
        ∈ Submodule.span (MonoidAlgebra K₀ X) (Set.range β) := by
    intro g k
    have h1 : (MonoidAlgebra.single (1 : X) k : MonoidAlgebra K X)
        ∈ Submodule.span (MonoidAlgebra K₀ X) (Set.range β) := by
      rw [hc k]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have heq : (MonoidAlgebra.single g k : MonoidAlgebra K X)
        = (MonoidAlgebra.single g (1 : K₀) : MonoidAlgebra K₀ X) •
            (MonoidAlgebra.single (1 : X) k : MonoidAlgebra K X) := by
      rw [hJ]
      simp [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.single_mul_single]
    rw [heq]
    exact Submodule.smul_mem _ _ h1
  -- Spanning: write `m` as a finite sum of `single g (m.coeff g)`.
  have hspan : ⊤ ≤ Submodule.span (MonoidAlgebra K₀ X) (Set.range β) := by
    intro m _
    have hm : m = ∑ g ∈ m.coeff.support, MonoidAlgebra.single g (m.coeff g) := by
      simpa [Finsupp.sum] using (MonoidAlgebra.sum_coeff_single m).symm
    rw [hm]
    exact Submodule.sum_mem _ fun g _ => key2 g (m.coeff g)
  let B : Module.Basis (Fin (Module.finrank K₀ K)) (MonoidAlgebra K₀ X) (MonoidAlgebra K X) :=
    Module.Basis.mk hli hspan
  exact ⟨Module.Free.of_basis B, Module.Finite.of_basis B⟩

end Work.ORFinal.FiniteFree
