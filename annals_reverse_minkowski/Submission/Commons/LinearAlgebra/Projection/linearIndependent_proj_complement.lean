import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace Commons.LinearAlgebra.Projection

/- Projected-tail independence: E = EuclideanSpace ℝ (Fin n).  Let S be a real subspace of E
spanned by the independent family `u : Fin d → E`, and let `v : Fin r → E` complete `u` to an
R-independent family `Sum.elim u v : Fin d ⊕ Fin r → E`.  Then the orthogonal projections of
the `v j` onto the orthogonal complement of S are again R-linearly independent:

    LinearIndependent ℝ (fun j : Fin r => (Submodule.orthogonal S).starProjection (v j)).

PROOF: suppose `Σ j, c j • p (v j) = 0` with `p := (Submodule.orthogonal S).starProjection`.
By linearity `p (Σ j, c j • v j) = 0`, so `w := Σ j, c j • v j` lies in the kernel of p,
which is S (the double-orthogonal of S is S: `Submodule.orthogonal_orthogonal`; kernel of the
projection onto Sᗮ is (Sᗮ)ᗮ = S: use `Submodule.ker_starProjection`).  Since
`S = span(u)`, `w` is an R-linear combination of the `u i`: `w = Σ i, a i • u i` for some
`a : Fin d → ℝ` (show membership in the span gives such coefficients - e.g. via
`Submodule.mem_span_range_iff_exists_fun_eq_sum`-style facts or
`LinearIndependent` machinery).  Then `Σ j, c j • v j - Σ i, a i • u i = 0`, an R-linear
relation among the independent family `Sum.elim u v`, so all `c j = 0` (use
`LinearIndependent` on the sum-type family; note the `u`-coefficients appear on the
`Sum.inl` side and the `v`-coefficients on `Sum.inr`).  Done.
Mathlib API hints: `Submodule.orthogonal_orthogonal`, `Submodule.ker_starProjection`,
`LinearIndependent` (and its use with sums over Finset.univ), `Submodule.span`,
`Finset.univ`, `real_inner_smul_left` if needed.  Keep the statement exactly as given. -/
theorem linearIndependent_proj_complement {n d r : ℕ}
    (u : Fin d → EuclideanSpace ℝ (Fin n)) (v : Fin r → EuclideanSpace ℝ (Fin n))
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hS : S = Submodule.span ℝ (Set.range u))
    (hf : LinearIndependent ℝ (Sum.elim u v)) :
    LinearIndependent ℝ (fun j : Fin r => (Submodule.orthogonal S).starProjection (v j)) := by
  classical
  let p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Submodule.orthogonal S).starProjection
  have hpker : p.ker = S := by
    simp [p, Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- p is linear, so p (∑ j, c j • v j) = ∑ j, c j • p (v j) = 0.
  have hpw : p (∑ j : Fin r, c j • v j) = 0 := by
    calc
      p (∑ j : Fin r, c j • v j) = ∑ j : Fin r, p (c j • v j) := by simp
      _ = ∑ j : Fin r, c j • p (v j) := by simp
      _ = 0 := by simpa [p] using hc
  -- Hence w := ∑ j, c j • v j lies in the kernel of p, which equals S = span (range u).
  have hwS : (∑ j : Fin r, c j • v j) ∈ S := by
    have hwker : (∑ j : Fin r, c j • v j) ∈ p.ker := (LinearMap.mem_ker).2 hpw
    simpa [hpker] using hwker
  have hwspan : (∑ j : Fin r, c j • v j) ∈ Submodule.span ℝ (Set.range u) := by
    simpa [hS] using hwS
  -- Membership in span (range u) gives coefficients a : Fin d → ℝ with w = ∑ i, a i • u i.
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := u)).mp hwspan with ⟨a, ha⟩
  -- The whole family Sum.elim u v is independent; use its fintype formulation.
  have hf' : ∀ g : Fin d ⊕ Fin r → ℝ,
      (∑ x : Fin d ⊕ Fin r, g x • Sum.elim u v x) = 0 →
        ∀ x : Fin d ⊕ Fin r, g x = 0 :=
    Fintype.linearIndependent_iff.mp hf
  -- The coefficients (Sum.elim (fun i => -a i) c) give a linear relation.
  have hrel : (∑ x : Fin d ⊕ Fin r,
      (Sum.elim (fun i : Fin d => -a i) c x) • Sum.elim u v x) = 0 := by
    calc
      (∑ x : Fin d ⊕ Fin r,
          (Sum.elim (fun i : Fin d => -a i) c x) • Sum.elim u v x)
          = (∑ i : Fin d, (-a i) • u i) + ∑ j : Fin r, c j • v j := by
              rw [Fintype.sum_sum_type]
              rfl
      _ = -(∑ i : Fin d, a i • u i) + (∑ j : Fin r, c j • v j) := by
              congr 1
              simp
      _ = 0 := by
              rw [ha]
              simp
  intro j
  exact hf' (Sum.elim (fun i : Fin d => -a i) c) hrel (Sum.inr j)

end Commons.LinearAlgebra.Projection