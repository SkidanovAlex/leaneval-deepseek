import Mathlib
import Submission.Work.SSGRoute.E7Fin.corH2_injective_ptorsion_pt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne (1.1b): `corH2` is injective on the `p`-torsion (via the local transport)

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` over `k`, an open
subgroup `U ≤ D_A = decomp k A` of finite index and a prime `p ∣ [D_A : U]`, the corestriction

  `corH2 U hU (Ωˣ) : H²(U, Ωˣ) → H²(D_A, Ωˣ)`

is injective on the `p`-torsion.  This is the class-formation axiom (Milne, *ADT*, (1.1b)) in the
form needed by the `α²`-dévissage of the base case of the local duality theorem.

## The route

The whole arithmetic content is the local field `κ = k_𝔭`: `H²(D_A, Ωˣ) ≅ Br(κ) ≅ ℚ/ℤ` and
`cor : Br(M) → Br(κ)` is the identity in invariant coordinates, hence injective — in particular on
the `p`-torsion.  The transport of that local statement to `D_A` is carried out in the workspace by

* `Work.SSGRoute.PT.local_resH2_mu_eq_zero` — the `μ_n`-coefficient restriction statement at the
  local field `Q.adicCompletion K` (from the proved `Ωˣ`-coefficient
  `Work.SSGRoute.PT.local_resH2_eq_zero_of_index_nsmul_eq_zero` via the Kummer sequence);
* `Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv_general` — the compatibility of
  the identification `D_A ≅ Gal(κ̄/κ)` with `μ_n`, for arbitrary `n` (not just primes);
* `Work.SSGRoute.E7Fin.resH2_mu_eq_zero_decomp_pt` — the resulting statement
  `res_U` kills the index-torsion of `H²(D_A, μ_n)`;
* `Work.SSGRoute.E7Fin.corH2_injective_ptorsion_pt` — Milne (1.1b) at `D_A`.

The final step is the elementary group-theoretic argument of `E7Fin`: if `B = H²(D_A, Ωˣ)` is
divisible, `res_U` kills the `p^a`-torsion of `B` (`p^a ∥ [D_A : U]`), and `B[p] ≠ 0`, then
`cor(res b') = [D_A : U] · b' = (n/p^a) · b ≠ 0` for `b'` with `p^a b' = b`, so `cor` is non-zero
on `A[p] = H²(U, Ωˣ)[p]`; since `#A[p] = p` this forces injectivity.

## The statement proved here

`Work.SSGRoute.PT.corH2_injective_on_ptorsion_localTransport` is the `Fact`-free restatement of
`Work.SSGRoute.E7Fin.corH2_injective_ptorsion_of_dvd_index_pt` (the prime hypothesis is a plain
`p.Prime` here rather than a type class), with the last two arguments uncurried; the proof is
therefore the direct invocation of the latter.
-/

namespace Work.SSGRoute.PT

theorem corH2_injective_on_ptorsion_localTransport (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (p : ℕ) (hp : p.Prime) (hpdiv : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U)) :
    ∀ y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), p • y = 0 →
      Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) y = 0 → y = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro y hy hcor
  exact Work.SSGRoute.E7Fin.corH2_injective_ptorsion_of_dvd_index_pt
    k Ω A hA U hU p hpdiv y hy hcor

end Work.SSGRoute.PT
