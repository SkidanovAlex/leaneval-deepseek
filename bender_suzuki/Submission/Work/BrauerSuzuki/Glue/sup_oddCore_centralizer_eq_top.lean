import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glue: `O(G) C_G(t) = G` when the involution `t` is central modulo `O(G)`

Let `G` be finite, `t` an involution (`orderOf t = 2`) with `[t, g] = t g t⁻¹ g⁻¹ ∈ O(G)`
for every `g : G` (`O(G) = oddCore G` the largest normal subgroup of odd order).  Then `t`
is central in `G / O(G)`, and we prove `O(G) ⊔ C_G(t) = ⊤`.

The argument is elementary and does not need Schur–Zassenhaus even though the underlying
cohomological statement is `H¹(⟨t⟩, O(G)) = 0` for the coprime action of an involution.

For `g : G` put `k = [t, g] = t g t⁻¹ g⁻¹ ∈ O(G)` and `m = orderOf k` (odd, since `O(G)` has
odd order), `j = m / 2`, `n = (k ^ j)⁻¹ ∈ O(G)`.  Then `t k t⁻¹ = k⁻¹` (direct computation,
using `t⁻¹ = t`), hence `t k ^ j t⁻¹ = (k ^ j)⁻¹` and therefore

`t n t⁻¹ = k ^ j`,   while   `k ^ j * k = (k ^ j)⁻¹ = n`   (as `2 j + 1 = m`).

So `t (n g) t⁻¹ = (t n t⁻¹)(t g t⁻¹) = k ^ j · (k g) = (k ^ j · k) g = n g`, i.e.
`n · g ∈ C_G(t)`, and `g = n⁻¹ (n g) ∈ O(G) ⊔ C_G(t)`.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki.Glue

open Submission.Blueprint

theorem sup_oddCore_centralizer_eq_top {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (h : ∀ g : G, t * g * t⁻¹ * g⁻¹ ∈ Submission.Blueprint.oddCore G) :
    Submission.Blueprint.oddCore G ⊔ Subgroup.centralizer ({t} : Set G) = ⊤ := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine le_antisymm le_top ?_
  intro g _
  set N : Subgroup G := Submission.Blueprint.oddCore G with hN
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  -- `k = [t,g]` lies in `O(G)` and is inverted by conjugation with `t`.
  set k : G := t * g * t⁻¹ * g⁻¹ with hk
  have hkN : k ∈ N := by rw [hk, hN]; exact h g
  have hkconj : t * k * t⁻¹ = k⁻¹ := by
    rw [hk, htinv]
    have e1 : t * (t * g * t * g⁻¹) * t = g * t * g⁻¹ * t := by
      rw [show t * (t * g * t * g⁻¹) * t = (t * t) * g * t * g⁻¹ * t by group]
      rw [ht2, one_mul]
    have e2 : (t * g * t * g⁻¹)⁻¹ = g * t * g⁻¹ * t := by
      rw [show (t * g * t * g⁻¹)⁻¹ = g * t⁻¹ * g⁻¹ * t⁻¹ by group]
      rw [htinv]
    rw [e1, e2]
  have htg : t * g * t⁻¹ = k * g := by rw [hk, htinv]; group
  -- `m = orderOf k` is odd.
  set m : ℕ := orderOf k with hm
  have hm_odd : Odd m := by
    rw [hm]
    have hdiv : orderOf (⟨k, hkN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have hcoeeq : orderOf (⟨k, hkN⟩ : N) = orderOf k := (Subgroup.orderOf_coe _).symm
    rw [hcoeeq] at hdiv
    have hmodd : Odd (Nat.card N) := by
      rw [hN]; exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
    exact Odd.of_dvd_nat hmodd hdiv
  -- arithmetic: `j = m / 2` satisfies `2 j + 1 = m`.
  set j : ℕ := m / 2 with hjdef
  have hj : 2 * j + 1 = m := by
    rw [hjdef]
    have h' := Nat.div_add_mod m 2
    rw [Nat.odd_iff.mp hm_odd] at h'
    omega
  -- conjugation with `t` inverts every power of `k`.
  have hpow : ∀ i : ℕ, t * k ^ i * t⁻¹ = (k ^ i)⁻¹ := by
    intro i
    calc t * k ^ i * t⁻¹ = (MulAut.conj t) (k ^ i) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj t) k) ^ i := by rw [map_pow]
      _ = (k⁻¹) ^ i := by rw [MulAut.conj_apply, hkconj]
      _ = (k ^ i)⁻¹ := by rw [inv_pow]
  -- the correcting element `n = (k ^ j)⁻¹ ∈ O(G)`.
  set n : G := (k ^ j)⁻¹ with hn
  have hnN : n ∈ N := by rw [hn]; exact N.inv_mem (N.pow_mem hkN j)
  have hconjn : t * n * t⁻¹ = k ^ j := by
    rw [hn]
    have h2 : t * (k ^ j)⁻¹ * t⁻¹ = (t * k ^ j * t⁻¹)⁻¹ := by group
    rw [h2, hpow j, inv_inv]
  have hkey : k ^ j * k = n := by
    rw [hn]
    have h1 : k ^ (j + 1) * k ^ j = 1 := by
      rw [← pow_add]
      have : j + 1 + j = m := by omega
      rw [this, hm]
      exact pow_orderOf_eq_one k
    have h2 : k ^ (j + 1) = (k ^ j)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [pow_succ] at h2
    exact h2
  -- `n * g` is centralised by `t`.
  have hcomm : t * (n * g) = (n * g) * t := by
    have h1 : t * (n * g) * t⁻¹ = n * g := by
      calc t * (n * g) * t⁻¹ = (t * n * t⁻¹) * (t * g * t⁻¹) := by group
        _ = k ^ j * (k * g) := by rw [hconjn, htg]
        _ = (k ^ j * k) * g := by group
        _ = n * g := by rw [hkey]
    calc t * (n * g) = (t * (n * g) * t⁻¹) * t := by group
      _ = (n * g) * t := by rw [h1]
  have hngC : n * g ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hcomm
  have hg : g ∈ N ⊔ C := by
    have heq : g = n⁻¹ * (n * g) := by group
    rw [heq]
    exact Subgroup.mul_mem_sup (N.inv_mem hnN) hngC
  exact hg

end Work.BrauerSuzuki.Glue
