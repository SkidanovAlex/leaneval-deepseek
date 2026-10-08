import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.SZUtil.conj_of_index_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Complements of a normal subgroup of prime index are conjugate inside the subgroup

Let `N` be a normal subgroup of a finite group `X` with `[X : N] = p` prime and
`|N|` coprime to `p`.  If `U` and `V` are both complements of `N` in `X`, then `V` is the
conjugate of `U` by an element `n ∈ N`.

The proof is the prime-index case of Schur–Zassenhaus: `U` and `V` are Sylow `p`-subgroups of
`X`, hence conjugate by some `g : X`.  Since `X = N U`, write `g = n * u` with `n ∈ N`,
`u ∈ U`; conjugating by `u ∈ U` leaves `U` invariant, so `V = U ^ n` with `n ∈ N`.
-/

open scoped Pointwise

namespace Work.Coprime

theorem complement_conj_prime_index {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (p : ℕ) (hp : p.Prime) (hindex : N.index = p) (hcop : (Nat.card N).Coprime p)
    {U V : Subgroup X} (hU : N.IsComplement' U) (hV : N.IsComplement' V) :
    ∃ n ∈ N, V = U.map (MulAut.conj n).toMonoidHom := by
  have hcop' : (Nat.card N).Coprime N.index := by rw [hindex]; exact hcop
  have hp' : N.index.Prime := by rw [hindex]; exact hp
  -- Schur–Zassenhaus in the prime-index case: `U` and `V` are conjugate by some `g : X`.
  obtain ⟨g, hg⟩ := SZUtil.conj_of_index_prime hcop' hp' hU hV
  -- Since `X = N * U`, write `g = n * u` with `n ∈ N`, `u ∈ U`.
  have hgmem : g ∈ (N : Set X) * (U : Set X) := by
    rw [hU.mul_eq]; exact Set.mem_univ g
  obtain ⟨n, hn, u, hu, hnu⟩ := Set.mem_mul.mp hgmem
  refine ⟨n, hn, ?_⟩
  rw [hg]
  -- Conjugation by `u ∈ U` fixes `U`, so `U ^ g = U ^ n`.
  have hkey : MulAut.conj g • (U : Subgroup X) = MulAut.conj n • (U : Subgroup X) := by
    rw [← hnu, map_mul, mul_smul, Subgroup.conj_smul_eq_self_of_mem (H := U) hu]
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def] at hkey
  exact hkey

end Work.Coprime
