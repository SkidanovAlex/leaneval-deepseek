import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-! ## Auxiliary material for `Work.BW.rayHilb_cut`

Multiplication by a multihomogeneous element `Q` of multidegree `k • D` and the multigraded
component computation that underlies the exact sequence
`0 → (R/I)_{tD} →·Q (R/I)_{(t+k)D} → (R/(I,Q))_{(t+k)D} → 0`.
-/

/-- For `Q` multihomogeneous of multidegree `q`, the multidegree-`(e + q)` component of a product
`r * Q` is the multidegree-`e` component of `r`, times `Q`. (The relevant weight is `mdeg N`: both
variables of the `i`-th factor of `(P¹)^{N+1}` have weight `eᵢ`.) -/
theorem mul_whc_cut {N : ℕ} (Q : MR N) {q : Fin (N + 1) →₀ ℕ} (hQ : Q ∈ homPiece N q)
    (r : MR N) (e : Fin (N + 1) →₀ ℕ) :
    MvPolynomial.weightedHomogeneousComponent (mdeg N) (e + q) (r * Q) =
      MvPolynomial.weightedHomogeneousComponent (mdeg N) e r * Q := by
  have hQh : MvPolynomial.IsWeightedHomogeneous (mdeg N) Q q := by
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule] at hQ; exact hQ
  have hfin : (Function.support
      (fun m => MvPolynomial.weightedHomogeneousComponent (mdeg N) m r)).Finite :=
    MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) r
  have hsum : (∑ m ∈ Set.Finite.toFinset hfin,
      MvPolynomial.weightedHomogeneousComponent (mdeg N) m r) = r := by
    rw [← finsum_eq_sum _ hfin]
    exact MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) r
  have hW : ∀ m, MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) m r) m :=
    fun m => (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ (mdeg N) m _).mp
      (MvPolynomial.weightedHomogeneousComponent_mem (mdeg N) r m)
  conv_lhs => rw [← hsum]
  rw [Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single e]
  · exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same ((hW e).mul hQh)
  · intro b _ hne
    apply MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne (e + q)
    · exact (hW b).mul hQh
    · intro h; exact hne (add_right_cancel h).symm
  · intro he
    have he' : e ∉ Function.support
        (fun m => MvPolynomial.weightedHomogeneousComponent (mdeg N) m r) := by
      simpa [Set.Finite.mem_toFinset] using he
    simp only [Function.mem_support, not_not] at he'
    rw [he', zero_mul, map_zero]

/-- Multiplication by `Q ∈ homPiece N (k • D)` as a `ℂ`-linear map
`(R)_{tD} → (R)_{(t+k)D}` (multiplication by a multihomogeneous element raises the multidegree by
`k • D`). -/
noncomputable def mulQ {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (k : ℕ) (Q : MR N)
    (hQ : Q ∈ homPiece N (k • D)) (t : ℕ) :
    ↥(homPiece N (t • D)) →ₗ[ℂ] ↥(homPiece N ((t + k) • D)) where
  toFun x := ⟨Q * x.1, by
    have hQ' : Q ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) (k • D) := hQ
    have hx : x.1 ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) (t • D) := x.2
    have hmem := (MvPolynomial.weightedHomogeneousSubmodule_mul (mdeg N) (k • D) (t • D))
      (Submodule.mul_mem_mul hQ' hx)
    rwa [add_comm (k • D) (t • D), ← add_smul] at hmem⟩
  map_add' x y := by
    ext
    simp [mul_add]
  map_smul' c x := by
    ext
    simp

@[simp]
theorem mulQ_apply {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (k : ℕ) (Q : MR N)
    (hQ : Q ∈ homPiece N (k • D)) (t : ℕ) (x : ↥(homPiece N (t • D))) :
    ((mulQ D k Q hQ t x : ↥(homPiece N ((t + k) • D))) : MR N) = Q * x.1 := rfl

end Work.BW
