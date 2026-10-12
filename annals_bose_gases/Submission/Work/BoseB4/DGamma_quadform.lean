import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Bomb_symm
import Submission.Work.BoseB4.Cre_ann_adjoint
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.DGamma_quadform` — the quadratic form of a second-quantised one-particle operator

FS `lem:2ndQuand` gives the kinetic energy in the form

    `∑_j 𝒯'_j = ∑_k τ(k) a_k† a_k`,

and it is *consumed* on a fixed state `Φ` (of finitely many particles), where it reads

    `⟪Φ, ∑_j 𝒯'_j Φ⟫ = ∑_k τ(k) ‖a_k Φ‖²`.

This module performs exactly that second step in the abstract coordinate model
`RealFock m = (Fin m →₀ ℕ) →₀ ℝ` with the Bombieri form `bomb m`:

* `dGamma m T = ∑_{ij} (T e_j)_i · a_i†a_j` (`Work.BoseB4.DGamma`) is the second
  quantisation of the one-particle operator `T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)`;
* `bomb m (dGamma m T Φ) Φ = ∑_{ij} (T e_j)_i · ⟪a_i Φ, a_j Φ⟫` always
  (`Work.BoseB4.bomb_dGamma_expand` below), because `a_i†` is the `bomb`-adjoint of
  `a_i` (`Work.BoseB4.Cre_ann_adjoint`) and `bomb` is symmetric
  (`Work.BoseB4.Bomb_symm`);
* if `T` is diagonal in the coordinate basis, `T e_j = λ_j e_j`, the matrix
  elements collapse to `(T e_j)_i = λ_j δ_{ij}` and the double sum to the diagonal:

      `bomb m (dGamma m T Φ) Φ = ∑_i λ_i · bomb m (ann m i Φ) (ann m i Φ)`

  which is `Work.BoseB4.DGamma_quadform`, the form in which the corpus consumes
  FS's `lem:2ndQuand` row `∑_j 𝒯'_j = ∑_k τ(k) a_k†a_k`.

Since `T` is a real linear map on `Fin m → ℝ` which is diagonalised by the
coordinate basis, `h` below is nothing but the Fourier/eigenbasis identification of
the box's one-particle operator `𝒯'` with multiplication by `τ(k)` — the box-side
computation that node B4 takes as its input.
-/

open scoped BigOperators

namespace Work.BoseB4

/-- **The quadratic form of `dGamma` on a general one-particle operator.**  For
*any* `T`, `bomb m (dGamma m T Φ) Φ` is the double sum of the matrix elements of
`T` against the `bomb`-pairings of the annihilated state.  This is the fully
general expansion (no diagonalisation needed); the diagonal case is
`Work.BoseB4.DGamma_quadform`.

The two ingredients are the `bomb`-adjointness `a_i† = (a_i)*`
(`Cre_ann_adjoint`) and the symmetry of `bomb` (`Bomb_symm`), which together turn
`⟪a_i† a_j Φ, Φ⟫` into `⟪a_i Φ, a_j Φ⟫`. -/
theorem bomb_dGamma_expand {m : ℕ} (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Φ : RealFock m) :
    bomb m (dGamma m T Φ) Φ
      = ∑ i : Fin m, ∑ j : Fin m,
          (T (evec m j) i) * bomb m (ann m i Φ) (ann m j Φ) := by
  -- `dGamma m T = ∑_i ∑_j (T e_j)_i • (a_i† ∘ a_j)`: apply it to `Φ`, push the
  -- sums and scalars out of the first argument of the (linear) form `bomb m`.
  simp only [dGamma, map_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  -- `a_i†` is the `bomb`-adjoint of `a_i`; then `bomb` is symmetric.
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, Cre_ann_adjoint, Bomb_symm]

/-- **The quadratic form of `dGamma` on a diagonalised one-particle operator.**
If `T` is diagonal in the coordinate basis `evec m i` with eigenvalues `lam i`
(the Fourier/eigenbasis identification of the box's one-particle kinetic operator),
then `bomb m (dGamma m T Φ) Φ` is the diagonal sum `∑_i lam i ‖a_i Φ‖²`.

This is FS `lem:2ndQuand`'s row `∑_j 𝒯'_j = ∑_k τ(k) a_k†a_k` in the quadratic form
in which it is used. -/
theorem DGamma_quadform {m : ℕ} (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (lam : Fin m → ℝ)
    (h : ∀ i : Fin m, T (Work.BoseB4.evec m i) = lam i • Work.BoseB4.evec m i)
    (Φ : Work.BoseB4.RealFock m) :
    Work.BoseB4.bomb m (Work.BoseB4.dGamma m T Φ) Φ
      = ∑ i : Fin m, lam i * Work.BoseB4.bomb m (Work.BoseB4.ann m i Φ) (Work.BoseB4.ann m i Φ) := by
  -- The matrix elements of `T` in the basis `e_j`: `(T e_j)_i = λ_j δ_{ij}`.
  have hT : ∀ i j : Fin m, T (evec m j) i = lam j * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    rw [h j, Pi.smul_apply]
    congr 1
    simp [evec, Pi.single_apply]
  rw [bomb_dGamma_expand]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- in the inner sum over `j` only `j = i` survives.
  refine (Finset.sum_congr rfl (fun j _ => by rw [hT i j])).trans ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

end Work.BoseB4
