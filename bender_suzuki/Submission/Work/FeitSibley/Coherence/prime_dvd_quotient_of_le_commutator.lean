import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `prime_dvd_quotient_of_le_commutator`

If `A` is a finite nilpotent group, `N ⊴ A` with `N ≤ [A, A]`, and `q` is a prime dividing
`|A|`, then `q` divides `|A ⧸ N|`.

The mechanism is that in a finite nilpotent group the derived subgroup cannot contain a full
Sylow `q`-subgroup.  Indeed, a finite nilpotent group `A` has a normal subgroup `H` of index `q`
for every prime `q` dividing `|A|` (`Group.IsNilpotent.exists_normal_index_eq_of_dvd_card`);
since `A ⧸ H` has prime order `q` it is commutative, so `[A, A] ≤ H`.  Hence `N ≤ H`, and
index divisibility gives `q = H.index ∣ N.index = |A ⧸ N|`.
-/

set_option linter.style.haveILetI false

namespace Work.FeitSibley.Coherence

theorem prime_dvd_quotient_of_le_commutator {A : Type} [Group A] [Finite A]
    [Group.IsNilpotent A] (N : Subgroup A) [N.Normal] (hN : N ≤ ⁅(⊤ : Subgroup A), ⊤⁆)
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ Nat.card A) : q ∣ Nat.card (A ⧸ N) := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- A normal subgroup `H` of index `q`.
  obtain ⟨H, hHidx, hHnorm⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := A) hqdvd
  haveI : H.Normal := hHnorm
  -- `A ⧸ H` has prime order `q`, hence is commutative.
  have hcard : Nat.card (A ⧸ H) = q := by
    rw [← Subgroup.index_eq_card H, hHidx]
  have hcomm : IsMulCommutative (A ⧸ H) :=
    (isCyclic_of_prime_card hcard).isMulCommutative
  -- Therefore `[A, A] ≤ H`.
  have hderiv : ⁅(⊤ : Subgroup A), ⊤⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm g₁ g₂
  -- `N ≤ [A, A] ≤ H`, so `q = H.index` divides `N.index = |A ⧸ N|`.
  have hNH : N ≤ H := hN.trans hderiv
  have hdvd : H.index ∣ N.index := Subgroup.index_dvd_of_le hNH
  rwa [hHidx, Subgroup.index_eq_card N] at hdvd

end Work.FeitSibley.Coherence
