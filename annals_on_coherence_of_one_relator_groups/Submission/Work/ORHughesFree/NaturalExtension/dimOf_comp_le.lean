import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.ModuleDim

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The matrix (in the `toLinearMapRight'` identification) of a composite is the product of the
matrices in the *reversed* order: `toLinearMapRight'` is a contravariant identification, so
`symm (b ∘ₗ a) = symm a * symm b`. -/
private lemma toLinearMapRight'_symm_comp {R : Type*} [Ring R] {p q r : ℕ}
    (a : (Fin p → R) →ₗ[R] (Fin q → R)) (b : (Fin q → R) →ₗ[R] (Fin r → R)) :
    Matrix.toLinearMapRight'.symm (b ∘ₗ a)
      = Matrix.toLinearMapRight'.symm a * Matrix.toLinearMapRight'.symm b := by
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'_mul]
  simp

/-- A linear map does not increase the dimension: for `φ : R^n → R^m` and a finite family
`v : Fin k → R^n`, the family of images `φ ∘ v` spans a submodule of dimension at most that
spanned by `v`.

Writing `W = span (range v) ≤ R^n` and `e`, `f` for the idempotent projections of `R^n`, `R^m`
onto `W` and onto `φ(W) = span (range (φ ∘ v))`, the composite `g = φ ∘ e` has range `φ(W)`, the
same as `f`.  Since `R^n` is free, `g` admits a (set-theoretic, not necessarily canonical) section
`σ` with `g ∘ σ = f`; passing to matrices this says
`symm f = symm σ * symm g = symm σ * (symm e * symm φ)`, and two applications of `(SMat2)` give
`rk (symm f) ≤ rk (symm g) ≤ rk (symm e)`. -/
theorem dimOf_comp_le {R : Type u} [Ring R] [VonNeumannRegularRing R] (rk : SylvesterRank R)
    {n m k : ℕ} (φ : (Fin n → R) →ₗ[R] (Fin m → R)) (v : Fin k → (Fin n → R)) :
    dimOf rk (fun j => φ (v j)) ≤ dimOf rk v := by
  classical
  obtain ⟨e, he, hre⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux v
  obtain ⟨f, hf, hrf⟩ :=
    Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux (fun j => φ (v j))
  rw [← dimOf_eq rk (fun j => φ (v j)) f hf hrf, ← dimOf_eq rk v e he hre]
  -- Goal: `dimOfEnd rk f ≤ dimOfEnd rk e`.
  set g : (Fin n → R) →ₗ[R] (Fin m → R) := φ ∘ₗ e with hgdef
  -- The range of `g = φ ∘ e` is `φ (span (range v)) = span (range (φ ∘ v))`, the range of `f`.
  have hgr : LinearMap.range g = LinearMap.range f := by
    rw [hgdef, LinearMap.range_comp e φ, hre, Submodule.map_span, hrf]
    congr 1
    ext y
    simp [Set.mem_image, Set.mem_range]
  -- Each value of `f` on a standard basis vector can be hit by `g`.
  have hmem : ∀ i : Fin m, ∃ y : Fin n → R, g y = f (Pi.single i (1 : R)) := by
    intro i
    have h : f (Pi.single i (1 : R)) ∈ LinearMap.range f := LinearMap.mem_range_self f _
    rw [← hgr] at h
    exact h
  choose t ht using hmem
  -- Extend the choices to a linear section `σ` of `g` with `g ∘ σ = f`.
  let b : Module.Basis (Fin m) R (Fin m → R) := Pi.basisFun R (Fin m)
  let σ : (Fin m → R) →ₗ[R] (Fin n → R) := (b.constr ℕ) t
  have hσ : g ∘ₗ σ = f := by
    refine b.ext fun i => ?_
    show g (σ (b i)) = f (b i)
    rw [show σ (b i) = t i from Module.Basis.constr_basis b ℕ t i, ht i,
      show b i = Pi.single i (1 : R) from Pi.basisFun_apply R (Fin m) i]
  -- Matrix form: `symm f = symm σ * symm g = symm σ * (symm e * symm φ)`.
  have hmf : Matrix.toLinearMapRight'.symm f
      = Matrix.toLinearMapRight'.symm σ * Matrix.toLinearMapRight'.symm g := by
    rw [← hσ]
    exact toLinearMapRight'_symm_comp σ g
  have hmg : Matrix.toLinearMapRight'.symm g
      = Matrix.toLinearMapRight'.symm e * Matrix.toLinearMapRight'.symm φ := by
    rw [hgdef]
    exact toLinearMapRight'_symm_comp e φ
  simp only [dimOfEnd]
  rw [hmf, hmg]
  calc rk.rk m m (Matrix.toLinearMapRight'.symm σ *
        (Matrix.toLinearMapRight'.symm e * Matrix.toLinearMapRight'.symm φ))
      ≤ rk.rk n m (Matrix.toLinearMapRight'.symm e * Matrix.toLinearMapRight'.symm φ) :=
        rk.rk_mul_le_right _ _
    _ ≤ rk.rk n n (Matrix.toLinearMapRight'.symm e) := rk.rk_mul_le_left _ _

end Work.ORHughesFree.NaturalExtension
