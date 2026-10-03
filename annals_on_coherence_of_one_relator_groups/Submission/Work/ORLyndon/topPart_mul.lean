import Mathlib
import Submission.Work.ORLyndon.powDefs

/-!
# The top level part of a product is the product of the top level parts

Let `φ : G →* Multiplicative ℤ` be a "level" homomorphism on a group `G` and, for `k : ℤ`, let
`levelPart φ k a` be the sum of the terms of `a : R[G]` whose group element has level exactly `k`.
Since `φ` is a homomorphism, levels add under multiplication.  Hence if all the group elements
occurring in `a` have level `≤ N` and all those occurring in `b` have level `≤ M`, the terms of
`a * b` of level exactly `N + M` are precisely the products of a term of `a` of level `N` and a term
of `b` of level `M`:

`levelPart φ N a * levelPart φ M b = levelPart φ (N+M) (a * b)`.

This is the compatibility of the `σ_t`-level grading with the multiplication, used in the Magnus
step of the Cohen--Lyndon induction, with `φ = Work.ORLyndon.levelOf t r u l hpow hσ` the level map
of the `σ_t`-decomposition `G = ker (σ_t) ⋊ ⟨t̄⟩` of a one-relator group whose root `u` has vanishing
`t`-exponent sum.

The proof is a direct coefficient computation.  Writing `Ac` and `Bc` for the coefficient functions
of the two level parts, the coefficient of `g₀` in the left-hand side is
`∑_{h ∈ supp Ac} Ac h * Bc (h⁻¹ g₀)`, and that of the right-hand side is the same sum over the
support of `a` (when `φ g₀ = ofAdd (N+M)`) or `0`.  The two sums agree because

* for `h ∈ supp Ac` the level of `h` is `N`, so `Ac h = a.coeff h` and the level of `h⁻¹ g₀` is
  `-(N) + (N+M) = M`, whence `Bc (h⁻¹ g₀) = b.coeff (h⁻¹ g₀)`;
* for `h ∈ supp a` outside `supp Ac` the level of `h` is `< N`, so the level of `h⁻¹ g₀` is `> M`
  and `b.coeff (h⁻¹ g₀) = 0`;
* if instead `φ g₀ ≠ ofAdd (N+M)`, then for every `h ∈ supp Ac` the level of `h⁻¹ g₀` is different
  from `M`, so the sum vanishes.

The auxiliary statements are `private`: the module `Submission.Work.ORLyndon.levelPart_mul_top`
already provides the same general result publicly (`Work.ORLyndon.filter_mul_filter`,
`Work.ORLyndon.coeff_filter_mul_filter`), so this file introduces no new public name besides the
requested `Work.ORLyndon.topPart_mul`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The coefficient of a product of two level parts.**  If every group element in the support of
`a` has level `≤ N` and every group element in the support of `b` has level `≤ M`, then the
coefficient at `g₀` of the product of the two level parts is the coefficient of `g₀` in `a * b` if
the level of `g₀` is exactly `N + M`, and `0` otherwise. -/
private theorem coeff_filter_mul_filter_aux {G : Type*} [Group G] {R : Type*} [Semiring R]
    (φ : G →* Multiplicative ℤ) (N M : ℤ) (a b : R[G])
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (φ g).toAdd ≤ M) (g₀ : G) :
    ((MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff) :
          R[G]) *
        (MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff) :
          R[G])).coeff g₀
      = if φ g₀ = Multiplicative.ofAdd (N + M) then (a * b).coeff g₀ else 0 := by
  classical
  set Ac : G →₀ R := Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff with hAcdef
  set Bc : G →₀ R := Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff with hBcdef
  have hAc : ∀ h, Ac h = if φ h = Multiplicative.ofAdd N then a.coeff h else 0 := by
    intro h; rw [hAcdef, Finsupp.filter_apply]
  have hBc : ∀ h, Bc h = if φ h = Multiplicative.ofAdd M then b.coeff h else 0 := by
    intro h; rw [hBcdef, Finsupp.filter_apply]
  have hsupp : Ac.support ⊆ a.coeff.support := by
    intro h hh
    have hne : Ac h ≠ 0 := Finsupp.mem_support_iff.mp hh
    rw [hAc] at hne
    by_cases hp : φ h = Multiplicative.ofAdd N
    · exact Finsupp.mem_support_iff.mpr (by rwa [if_pos hp] at hne)
    · rw [if_neg hp] at hne; exact absurd rfl hne
  have hlev : ∀ h ∈ Ac.support, φ h = Multiplicative.ofAdd N := by
    intro h hh
    have hne : Ac h ≠ 0 := Finsupp.mem_support_iff.mp hh
    rw [hAc] at hne
    by_cases hp : φ h = Multiplicative.ofAdd N
    · exact hp
    · rw [if_neg hp] at hne; exact absurd rfl hne
  have hLsum : (MonoidAlgebra.ofCoeff Ac * MonoidAlgebra.ofCoeff Bc).coeff g₀
      = ∑ h ∈ Ac.support, Ac h * Bc (h⁻¹ * g₀) := by
    rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_ofCoeff,
      MonoidAlgebra.coeff_ofCoeff]
    exact Finsupp.sum_of_support_subset Ac (le_refl _) _ (fun i _ => by simp)
  have hRsum : (a * b).coeff g₀
      = ∑ h ∈ a.coeff.support, a.coeff h * b.coeff (h⁻¹ * g₀) := by
    rw [MonoidAlgebra.coeff_mul_apply_left]
    exact Finsupp.sum_of_support_subset a.coeff (le_refl _) _ (fun i _ => by simp)
  rw [hLsum, hRsum]
  by_cases hp : φ g₀ = Multiplicative.ofAdd (N + M)
  · rw [if_pos hp]
    have hpadd : (φ g₀).toAdd = N + M := by rw [hp, toAdd_ofAdd]
    have key : ∀ h ∈ Ac.support,
        Ac h * Bc (h⁻¹ * g₀) = a.coeff h * b.coeff (h⁻¹ * g₀) := by
      intro h hh
      have hφh : φ h = Multiplicative.ofAdd N := hlev h hh
      have h1 : Ac h = a.coeff h := by rw [hAc, if_pos hφh]
      have hφz : φ (h⁻¹ * g₀) = Multiplicative.ofAdd M := by
        rw [map_mul, map_inv, hφh, hp, ← ofAdd_neg, ← ofAdd_add,
          show -N + (N + M) = M from by ring]
      have h2 : Bc (h⁻¹ * g₀) = b.coeff (h⁻¹ * g₀) := by rw [hBc, if_pos hφz]
      rw [h1, h2]
    have zero : ∀ x ∈ a.coeff.support, x ∉ Ac.support →
        a.coeff x * b.coeff (x⁻¹ * g₀) = 0 := by
      intro x hx hxAc
      have hxa : a.coeff x ≠ 0 := Finsupp.mem_support_iff.mp hx
      have hle : (φ x).toAdd ≤ N := ha x hx
      have hneN : (φ x).toAdd ≠ N := by
        intro hc
        apply hxAc
        refine Finsupp.mem_support_iff.mpr ?_
        rw [hAc, if_pos (by rw [← ofAdd_toAdd (φ x), hc])]
        exact hxa
      have hlt : (φ x).toAdd < N := lt_of_le_of_ne hle hneN
      have hb0 : b.coeff (x⁻¹ * g₀) = 0 := by
        by_contra hne
        have hmem : x⁻¹ * g₀ ∈ b.coeff.support := Finsupp.mem_support_iff.mpr hne
        have hb' := hb _ hmem
        have hz : (φ (x⁻¹ * g₀)).toAdd = -(φ x).toAdd + (φ g₀).toAdd := by
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
        rw [hz, hpadd] at hb'
        linarith
      rw [hb0, mul_zero]
    rw [Finset.sum_congr rfl key, Finset.sum_subset hsupp zero]
  · rw [if_neg hp]
    refine Finset.sum_eq_zero (fun h hh => ?_)
    have hφh : φ h = Multiplicative.ofAdd N := hlev h hh
    have hz : Bc (h⁻¹ * g₀) = 0 := by
      by_contra hne
      have h1 : φ (h⁻¹ * g₀) = Multiplicative.ofAdd M := by
        by_contra hc
        rw [hBc, if_neg hc] at hne
        exact hne rfl
      refine hp ?_
      calc φ g₀ = φ (h * (h⁻¹ * g₀)) := by rw [mul_inv_cancel_left]
        _ = φ h * φ (h⁻¹ * g₀) := map_mul _ _ _
        _ = Multiplicative.ofAdd N * Multiplicative.ofAdd M := by rw [hφh, h1]
        _ = Multiplicative.ofAdd (N + M) := (ofAdd_add N M).symm
    rw [hz, mul_zero]

/-- **The top level parts multiply.**  If the levels of the terms of `a` are bounded above by `N`
and those of `b` by `M`, then the `N`-th level part of `a` times the `M`-th level part of `b` is
the `(N+M)`-th level part of `a * b`. -/
private theorem filter_mul_filter_aux {G : Type*} [Group G] {R : Type*} [Semiring R]
    (φ : G →* Multiplicative ℤ) (N M : ℤ) (a b : R[G])
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (φ g).toAdd ≤ M) :
    (MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff) :
        R[G]) *
      MonoidAlgebra.ofCoeff (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff) =
    MonoidAlgebra.ofCoeff
      (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd (N + M)) (a * b).coeff) := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext (fun g₀ => ?_))
  rw [coeff_filter_mul_filter_aux φ N M a b ha hb g₀]
  show (if φ g₀ = Multiplicative.ofAdd (N + M) then (a * b).coeff g₀ else 0) =
    (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd (N + M)) (a * b).coeff) g₀
  rw [Finsupp.filter_apply]

/-- The definition of `Work.ORLyndon.levelPart` read in the vocabulary of
`coeff_filter_mul_filter_aux`: the `k`-th level part is the coefficient function restricted to the
group elements of level exactly `k`. -/
private theorem levelPart_eq_ofCoeff {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ)
    (a : MonoidAlgebra K (OneRelatorGroup r)) :
    Work.ORLyndon.levelPart t r u l hpow hσ k a =
      MonoidAlgebra.ofCoeff (Finsupp.filter
        (fun g => Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd k) a.coeff) :=
  rfl

theorem topPart_mul {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
    {hσ : Work.OROneRel.sigma t u = 1} {a b : MonoidAlgebra K (OneRelatorGroup r)} {N M : ℤ}
    (ha : ∀ g ∈ a.coeff.support, (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (Work.ORLyndon.levelOf t r u l hpow hσ g).toAdd ≤ M) :
    Work.ORLyndon.levelPart t r u l hpow hσ N a * Work.ORLyndon.levelPart t r u l hpow hσ M b =
      Work.ORLyndon.levelPart t r u l hpow hσ (N + M) (a * b) := by
  rw [levelPart_eq_ofCoeff (K := K) t r u l hpow hσ N a,
    levelPart_eq_ofCoeff (K := K) t r u l hpow hσ M b,
    levelPart_eq_ofCoeff (K := K) t r u l hpow hσ (N + M) (a * b)]
  exact filter_mul_filter_aux (Work.ORLyndon.levelOf t r u l hpow hσ) N M a b ha hb

end Work.ORLyndon
