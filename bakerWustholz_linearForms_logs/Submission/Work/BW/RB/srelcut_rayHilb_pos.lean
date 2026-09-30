import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.rayHilb_finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BW.RB

open Work.BW

/-!
# Positivity of the ray Hilbert function along `tD`

For a multihomogeneous prime `r ⊂ ℂ[X_{i0}, X_{i1} : i]` whose zero locus is not swallowed by a
coordinate hyperplane `{X_{i0} = 0}` — precisely, such that the monomial
`∏ᵢ X_{i0}^{t Dᵢ}` (of multidegree `tD`) does not lie in `r` for any `t` — the `tD`-th
multigraded piece of the quotient `R ⧸ r` is nonzero.  Hence `rayHilb N D r t ≥ 1`: the monomial
itself is a nonzero element of the piece `homPiece N (tD)`, and a nonzero quotient over the field
`ℂ` has `finrank ≥ 1`.

This is the "cut" lemma feeding `Srel N D r = (N+1)! · rayDeg N D r` and its monotonicity
statements: it is what stops the ray Hilbert polynomial from collapsing to `0`.
-/

/-- The monomial `∏ᵢ X_{i0}^{dᵢ}` has multidegree `d`, hence lies in the piece `homPiece N d`. -/
private lemma prod_X_pow_mem_homPiece {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (d i)) ∈ homPiece N d := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hprod : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (d i))
      (∑ i : Fin (N + 1), (d i) • mdeg N (i, 0)) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod (R := ℂ) (σ := Fin (N + 1) × Fin 2)
      (ι := Fin (N + 1)) Finset.univ (fun i => MvPolynomial.X (i, 0) ^ (d i))
      (fun i => (d i) • mdeg N (i, 0))
    intro i _
    exact (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N) (i, 0)).pow (d i)
  convert hprod using 2
  ext j
  simp [mdeg, Finsupp.smul_single]

/-- If the ray monomial `∏ᵢ X_{i0}^{t Dᵢ}` avoids the prime `r`, the `tD`-th piece of `R ⧸ r`
is nonzero, i.e. `rayHilb N D r t ≥ 1`. -/
theorem srelcut_rayHilb_pos {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (r : Ideal (MR N)) (hr : r.IsPrime)
    (hav : ∀ t : ℕ, (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)) ∉ r)
    (t : ℕ) : 1 ≤ rayHilb N D r t := by
  -- The ray monomial of degree `tD` survives in `R ⧸ r`: it lies in the piece `homPiece N (tD)`
  -- and is not in `r`.
  set m : MR N := ∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i) with hm
  have hmem : m ∈ homPiece N (t • D) := by
    rw [hm]
    have h1 : (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i))
        = (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ ((t • D) i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    rw [h1]
    exact prod_X_pow_mem_homPiece (t • D)
  have hmnot : m ∉ r := by
    rw [hm]
    exact hav t
  -- Hence its class in the quotient is nonzero, so the quotient is nontrivial.
  have hneq : (Submodule.Quotient.mk (p := Submodule.comap (homPiece N (t • D)).subtype
      (r.restrictScalars ℂ)) ⟨m, hmem⟩ : ↥(homPiece N (t • D)) ⧸
      Submodule.comap (homPiece N (t • D)).subtype (r.restrictScalars ℂ)) ≠ 0 := by
    intro hzero
    rw [Submodule.Quotient.mk_eq_zero] at hzero
    exact hmnot (by simpa [Submodule.mem_comap] using hzero)
  have hfin : Module.Finite ℂ ↥(homPiece N (t • D)) := rayHilb_finite N (t • D)
  have hnt : Nontrivial (↥(homPiece N (t • D)) ⧸
      Submodule.comap (homPiece N (t • D)).subtype (r.restrictScalars ℂ)) :=
    nontrivial_of_ne _ _ hneq
  have hpos : 0 < rayHilb N D r t := by
    rw [rayHilb]
    exact Module.finrank_pos
  omega

end Work.BW.RB
