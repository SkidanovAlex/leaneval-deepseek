import Mathlib
import Submission.Commons.RingTheory.Ideal.card_minimalPrimes_homogeneous_le
import Submission.Commons.RingTheory.Ideal.card_minimalPrimes_quotient_eq
import Submission.Commons.RingTheory.Ideal.card_minimalPrimes_comap_eq
import Submission.Commons.RingTheory.Ideal.finite_subtype_minimalPrimes
import Submission.Commons.RingTheory.Ideal.isPrime_sup_span_X_sub_one
import Submission.Commons.RingTheory.Ideal.minimalPrimes_homogeneous
import Submission.Commons.Algebra.MvPolynomial.surjective_aeval_dehom
import Submission.Commons.Algebra.MvPolynomial.ker_aeval_dehom
import Submission.Commons.Algebra.MvPolynomial.exists_homogenization
import Submission.Commons.Algebra.MvPolynomial.span_range_homogeneousComponent_mem

/-!
# Bezout bound for the number of minimal primes of a complete intersection

If `f : Fin r → k[X_1,…,X_r]` is a family of polynomials, then the number of minimal primes
of `k[X_1,…,X_r]/(f_1,…,f_r)` is at most `∏ i, (deg f i).max 1`.

The proof homogenizes the `f i` to forms `F i` in `k[X_0,…,X_r]` and applies the projective
Bezout bound `card_minimalPrimes_homogeneous_le`, together with the fact that the affine chart
`X_0 = 1` does not increase the number of minimal primes.
-/

open MvPolynomial

namespace Commons.RingTheory.Ideal

section Bridge

variable {k : Type} [Field k] {n : ℕ}

/-- The number of minimal primes over `J ⊔ span{X 0 - 1}` is at most the number of minimal
primes over the homogeneous ideal `J`.  (A self-contained version of the proof, phrased with
the component-form homogeneity hypothesis so that it can be combined with the projective
Bezout bound.) -/
private theorem card_minimalPrimes_sup_le_aux
    (J : Ideal (MvPolynomial (Fin (n+1)) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) //
        p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes}
      ≤ Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) // p ∈ J.minimalPrimes} := by
  classical
  haveI : Finite {p : Ideal (MvPolynomial (Fin (n+1)) k) // p ∈ J.minimalPrimes} :=
    finite_subtype_minimalPrimes J
  have exists_below : ∀ (𝔔 : Ideal (MvPolynomial (Fin (n+1)) k)),
      𝔔 ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes →
      ∃ 𝔮 ∈ J.minimalPrimes, 𝔮 ≤ 𝔔 := by
    intro 𝔔 h𝔔
    haveI : 𝔔.IsPrime := h𝔔.isPrime
    exact Ideal.exists_minimalPrimes_le (I := J) (le_trans le_sup_left h𝔔.le)
  let g : {𝔔 : Ideal (MvPolynomial (Fin (n+1)) k) //
        𝔔 ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes} →
      {𝔮 : Ideal (MvPolynomial (Fin (n+1)) k) // 𝔮 ∈ J.minimalPrimes} :=
    fun 𝔔 => ⟨Classical.choose (exists_below 𝔔.1 𝔔.2),
      (Classical.choose_spec (exists_below 𝔔.1 𝔔.2)).1⟩
  have hg_le : ∀ 𝔔, (g 𝔔).1 ≤ 𝔔.1 := fun 𝔔 => (Classical.choose_spec (exists_below 𝔔.1 𝔔.2)).2
  have h_eq : ∀ 𝔔, (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}
      = 𝔔.1 := by
    intro 𝔔
    haveI : (g 𝔔).1.IsPrime := (g 𝔔).2.isPrime
    have hcomp : ∀ x ∈ (g 𝔔).1, ∀ j,
        MvPolynomial.homogeneousComponent j x ∈ (g 𝔔).1 :=
      minimalPrimes_homogeneous J hJ (g 𝔔).2
    have hXq : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) ∉ (g 𝔔).1 := by
      intro h
      have h1 : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) ∈ 𝔔.1 := hg_le 𝔔 h
      have h2 : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1 ∈ 𝔔.1 :=
        𝔔.2.le (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
      have h3 : (1 : MvPolynomial (Fin (n+1)) k) ∈ 𝔔.1 := by
        have := sub_mem h1 h2
        simpa using this
      exact 𝔔.2.isPrime.ne_top ((Ideal.eq_top_iff_one 𝔔.1).mpr h3)
    have hsup_prime := isPrime_sup_span_X_sub_one (g 𝔔).1 hcomp hXq
    have hle : (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} ≤ 𝔔.1 :=
      sup_le (hg_le 𝔔) (le_trans le_sup_right 𝔔.2.le)
    have hIle : J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} ≤
        (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} :=
      sup_le (le_trans (g 𝔔).2.le le_sup_left) le_sup_right
    have hmin : 𝔔.1 ≤ (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} :=
      (show Minimal (fun q => q.IsPrime ∧
          (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}) ≤ q) 𝔔.1
        from 𝔔.2).2 ⟨hsup_prime, hIle⟩ hle
    exact le_antisymm hle hmin
  exact Nat.card_le_card_of_injective g (by
    intro 𝔔1 𝔔2 h
    apply Subtype.ext
    have hv : (g 𝔔1).1 = (g 𝔔2).1 := congrArg Subtype.val h
    rw [← h_eq 𝔔1, ← h_eq 𝔔2, hv])

/-- Setting `X 0 = 1` does not increase the number of minimal primes of the quotient by a
homogeneous ideal. -/
private theorem card_minimalPrimes_sup_span_X_sub_one_le_aux
    (J : Ideal (MvPolynomial (Fin (n+1)) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})) //
        p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})))}
      ≤ Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J))} := by
  calc Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})))}
      = Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) //
          p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes} :=
        card_minimalPrimes_quotient_eq _
    _ ≤ Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) // p ∈ J.minimalPrimes} :=
        card_minimalPrimes_sup_le_aux J hJ
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J))} :=
        (card_minimalPrimes_quotient_eq J).symm

end Bridge

theorem card_minimalPrimes_quotient_le {k : Type} [Field k] {r : ℕ}
    (f : Fin r → MvPolynomial (Fin r) k) :
    Nat.card {p : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)) //
      p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)))}
      ≤ ∏ i, (f i).totalDegree.max 1 := by
  classical
  let φ : MvPolynomial (Fin (r+1)) k →ₐ[k] MvPolynomial (Fin r) k :=
    MvPolynomial.aeval
      (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i)
  have hφsurj : Function.Surjective φ := Commons.Algebra.MvPolynomial.surjective_aeval_dehom r
  have hφker : RingHom.ker φ.toRingHom =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1} :=
    Commons.Algebra.MvPolynomial.ker_aeval_dehom r
  choose F hFhom hFdeg hFdehom using fun i =>
    Commons.Algebra.MvPolynomial.exists_homogenization (f i)
  let J : Ideal (MvPolynomial (Fin (r+1)) k) := Ideal.span (Set.range F)
  have hJhom : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J :=
    Commons.Algebra.MvPolynomial.span_range_homogeneousComponent_mem F hFhom
  have hmap : Ideal.map φ.toRingHom J = Ideal.span (Set.range f) := by
    rw [show J = Ideal.span (Set.range F) from rfl, Ideal.map_span]
    have himg : ⇑φ.toRingHom '' Set.range F = Set.range f := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hFdehom i
    rw [himg]
  have hcomap : (Ideal.span (Set.range f)).comap φ.toRingHom
      = J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1} := by
    apply le_antisymm
    · intro g hg
      rw [Ideal.mem_comap] at hg
      rw [← hmap] at hg
      obtain ⟨j, hj, hjeq⟩ := (Ideal.mem_map_iff_of_surjective φ.toRingHom hφsurj).mp hg
      have hkerg : g - j ∈ RingHom.ker φ.toRingHom := by
        rw [RingHom.mem_ker, map_sub, hjeq, sub_self]
      rw [hφker] at hkerg
      have : g = j + (g - j) := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left hj) (Ideal.mem_sup_right hkerg)
    · rw [sup_le_iff]
      constructor
      · intro x hx
        rw [Ideal.mem_comap, ← hmap]
        exact Ideal.mem_map_of_mem _ hx
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
        have hX0 : φ.toRingHom (MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) = 1 := by
          show φ (MvPolynomial.X 0) = 1
          simp only [φ, MvPolynomial.aeval_X, Fin.cases_zero]
        rw [map_sub, map_one, hX0, sub_self]
        exact Submodule.zero_mem _
  have hmin : Nat.card {p : Ideal (MvPolynomial (Fin r) k) //
        p ∈ (Ideal.span (Set.range f)).minimalPrimes}
      = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k) //
        p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1}).minimalPrimes} := by
    rw [← card_minimalPrimes_comap_eq φ.toRingHom hφsurj (Ideal.span (Set.range f)), hcomap]
  calc Nat.card {p : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)) //
        p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)))}
      = Nat.card {p : Ideal (MvPolynomial (Fin r) k) //
          p ∈ (Ideal.span (Set.range f)).minimalPrimes} :=
        card_minimalPrimes_quotient_eq _
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k) //
          p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1}).minimalPrimes} := hmin
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k ⧸
            (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1})) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (r+1)) k ⧸
            (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1})))} :=
        (card_minimalPrimes_quotient_eq _).symm
    _ ≤ Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k ⧸ J) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (r+1)) k ⧸ J))} :=
        card_minimalPrimes_sup_span_X_sub_one_le_aux J hJhom
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k) // p ∈ J.minimalPrimes} :=
        card_minimalPrimes_quotient_eq J
    _ ≤ ∏ i, (F i).totalDegree.max 1 := by
        rw [← card_minimalPrimes_quotient_eq J]
        exact card_minimalPrimes_homogeneous_le F hFhom
    _ ≤ ∏ i, (f i).totalDegree.max 1 := by
        apply Finset.prod_le_prod
        · intro i _
          exact Nat.zero_le _
        · intro i _
          exact max_le_max_right 1 (hFdeg i)

end Commons.RingTheory.Ideal
