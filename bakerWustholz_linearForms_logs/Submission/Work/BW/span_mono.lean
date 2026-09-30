import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.homPiece_finrank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- The exponent vector of the monomial `mono N d b`: `X_{i,1}` gets exponent `b i` and `X_{i,0}`
gets exponent `d i - b i`. -/
noncomputable def expOf (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ) :
    (Fin (N + 1) × Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v : Fin (N + 1) × Fin 2 =>
    if v.2 = 0 then d v.1 - b v.1 else b v.1

@[simp] lemma expOf_apply_zero (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ)
    (i : Fin (N + 1)) : expOf N d b (i, 0) = d i - b i := by
  rw [expOf, Finsupp.equivFunOnFinite_symm_apply_apply]
  simp

@[simp] lemma expOf_apply_one (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ)
    (i : Fin (N + 1)) : expOf N d b (i, 1) = b i := by
  rw [expOf, Finsupp.equivFunOnFinite_symm_apply_apply]
  simp

lemma expOf_eq_sum (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ) :
    expOf N d b = ∑ i : Fin (N + 1),
      (Finsupp.single (i, 1) (b i) + Finsupp.single (i, 0) (d i - b i)) := by
  rw [expOf, Finsupp.equivFunOnFinite_symm_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp [add_comm]

lemma mono_eq_monomial (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ) :
    mono N d b = MvPolynomial.monomial (expOf N d b) 1 := by
  rw [mono, expOf_eq_sum]
  have h1 : (∏ i : Fin (N + 1),
        MvPolynomial.X (i, 1) ^ (b i) * MvPolynomial.X (i, 0) ^ (d i - b i) : MR N)
      = ∏ i : Fin (N + 1),
          MvPolynomial.monomial
            (Finsupp.single (i, 1) (b i) + Finsupp.single (i, 0) (d i - b i)) 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, mul_one]
  rw [h1, ← MvPolynomial.monomial_sum_one Finset.univ
    (fun i => Finsupp.single (i, 1) (b i) + Finsupp.single (i, 0) (d i - b i))]

lemma weight_expOf (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ)
    (hb : ∀ i, b i ≤ d i) : Finsupp.weight (mdeg N) (expOf N d b) = d := by
  ext i
  rw [weight_mdeg_apply, expOf_apply_zero, expOf_apply_one]
  exact Nat.sub_add_cancel (hb i)

/-- Given `m` of weighted degree `d`, the `X_{i,0}`-exponent of `m` is `d i` minus its
`X_{i,1}`-exponent. -/
lemma sub_eq_of_weight (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (m : (Fin (N + 1) × Fin 2) →₀ ℕ)
    (hm : Finsupp.weight (mdeg N) m = d) (i : Fin (N + 1)) : d i - m (i, 1) = m (i, 0) := by
  have h := DFunLike.congr_fun hm i
  rw [weight_mdeg_apply] at h
  omega

/-- The `X_{i,1}`-exponent of `m` is at most `d i` when `m` has weighted degree `d`. -/
lemma snd_le_of_weight (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (m : (Fin (N + 1) × Fin 2) →₀ ℕ)
    (hm : Finsupp.weight (mdeg N) m = d) (i : Fin (N + 1)) : m (i, 1) ≤ d i := by
  have h := DFunLike.congr_fun hm i
  rw [weight_mdeg_apply] at h
  omega

lemma expOf_surj (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (m : (Fin (N + 1) × Fin 2) →₀ ℕ)
    (hm : Finsupp.weight (mdeg N) m = d) : expOf N d (fun i => m (i, 1)) = m := by
  ext v
  show (if v.2 = 0 then d v.1 - m (v.1, 1) else m (v.1, 1)) = m v
  by_cases hv : v.2 = 0
  · rw [if_pos hv]
    have h2 : m v = m (v.1, 0) := by rw [← Prod.mk.eta (p := v), hv]
    rw [h2]
    exact sub_eq_of_weight N d m hm v.1
  · rw [if_neg hv]
    have hv1 : v.2 = 1 := Fin.eq_one_of_ne_zero v.2 hv
    have h2 : m v = m (v.1, 1) := by rw [← Prod.mk.eta (p := v), hv1]
    rw [h2]

/-- The monomials `mono N d b` with `bᵢ ≤ dᵢ` span the multihomogeneous piece `homPiece N d` of the coordinate ring of `(P¹)^{N+1}`: every monomial of multidegree `d` is `X^m` with `m(i,0) + m(i,1) = dᵢ`, i.e. `m = (bᵢ)` on the `X_{i,1}`-coordinates. -/
theorem span_mono (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    homPiece N d = Submodule.span ℂ
      (Set.range (fun b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} => mono N d b.1)) := by
  have hpiece : homPiece N d = MvPolynomial.restrictSupport ℂ (homIndexSet d) := by
    change MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d = _
    rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
    rfl
  rw [hpiece, MvPolynomial.restrictSupport_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    have hmw : Finsupp.weight (mdeg N) m = d := hm
    refine Submodule.subset_span ⟨⟨fun i => m (i, 1), fun i => ?_⟩, ?_⟩
    · exact snd_le_of_weight N d m hmw i
    · show mono N d (fun i => m (i, 1)) = monomial m 1
      rw [mono_eq_monomial, expOf_surj N d m hmw]
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact Submodule.subset_span
      ⟨expOf N d b.1, weight_expOf N d b.1 b.2, (mono_eq_monomial N d b.1).symm⟩

end Work.BW
