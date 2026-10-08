import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.conj_mem_hatNp_and_notMem
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.projEC_eq_self
import Submission.Work.Tame.alphaI2LM_apply_eq_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.conj_mul_notMem_Lhat`

Feit–Thompson, Chapter III, Lemma 9.1 (value part, p. 805–806).  Let `L̂` be tamely imbedded in the
finite group `X` with supporting subgroups `𝔎_1, …, 𝔎_n` (Definition 9.1), let `𝔇 ≠ ∅`, let
`L ∈ 𝔏_i = {L ∈ 𝔇 | C(L) ⊆ 𝔑_i}` be an element of the `i`-th set of Feit–Thompson p. 805 and let
`H ∈ 𝔎_i^#` commute with `L`.  Then the product `HL` (an element of `𝔄_L = L(𝔎_i ∩ C(L))`,
(9.2)) is **not** conjugate in `X` to any element of `L̂`.

This is exactly the input needed for the value computation of Lemma 9.1: for
`A ∈ 𝔄_L \ {L}` the induced class function `α^*` (induction from `𝔏 = N(L̂)`) vanishes at `A`,
because every summand of the induction formula is `α(xAx^{-1})` with `α ∈ 𝓒₀(L̂)`, which is
non-zero only for `xAx^{-1} ∈ L̂^#`.

## The argument

Write `A = HL`.  Suppose `A` were conjugate to `x ∈ L̂`; say `x = γ A γ^{-1}`, and put
`J = γ H γ^{-1}`, `K = γ L γ^{-1}`, so that `x = JK`, `J` and `K` commute, and
`orderOf J = orderOf H`, `orderOf K = orderOf L`.

* By Definition 9.1(ii)(d), applied to the element `z ∈ L̂^#`, the order of `z` divides
  `|C_𝔏(z)| = |𝔏 ⊓ C(z)|` (as `L̂ ⊆ 𝔏`), so `(|𝔎_i|, |z|) = 1`.  In particular
  `(|𝔎_i|, |L|) = 1` and `(|𝔎_i|, |x|) = 1`.
* `orderOf J = orderOf H ∣ |𝔎_i|` (as `H ∈ 𝔎_i`) and `orderOf K = orderOf L` is coprime to
  `|𝔎_i|`, hence `orderOf J` and `orderOf K` are coprime; so `|x| = |J|·|K|`.
* Thus `|J|` divides both `|x|` and `|𝔎_i|`; when `x ≠ 1` these are coprime by the first bullet,
  and when `x = 1` the product formula gives `|J| = 1` directly.  Hence `|J| = 1`, i.e. `H = 1`,
  conflict.
-/

namespace Work.Tame

open Classical

theorem conj_mul_notMem_Lhat {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty)
    {i : Fin n} {L : X} (hL : L ∈ Lset Lhat (Hs i)) {H : X} (hH : H ∈ Hs i) (hH1 : H ≠ 1)
    (hcomm : H * L = L * H) :
    ∀ x ∈ Lhat, ¬ IsConj (H * L) x := by
  -- Definition 9.1(ii)(d): for `z ∈ L̂^#`, `|z|` divides `|C_𝔏(z)|`, which is coprime to `|𝔎_i|`.
  have hcop : ∀ z : X, z ∈ Lhat → z ≠ 1 → (Nat.card (Hs i)).Coprime (orderOf z) := by
    intro z hz hz1
    have hzdvd : orderOf z ∣ Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({z} : Set X)) := by
      have hmem : z ∈ (Lgrp Lhat ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) :=
        ⟨h.sub_norm hz, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have h1 : orderOf (⟨z, hmem⟩ : ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({z} : Set X))) ∣
          Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({z} : Set X)) :=
        orderOf_dvd_natCard _
      simpa [Subgroup.orderOf_coe] using h1
    exact (h.supp_coprime_cent hne i z hz hz1).coprime_dvd_right hzdvd
  -- `L ∈ L̂^#` because `L ∈ 𝔏_i ⊆ 𝔇`.
  have hLhat : L ∈ Lhat := (mem_Dset.mp hL.1).1
  have hL1 : L ≠ 1 := (mem_Dset.mp hL.1).2.1
  have hcopL : (Nat.card (Hs i)).Coprime (orderOf L) := hcop L hLhat hL1
  -- `|H|` divides `|𝔎_i|`.
  have hHdvd : orderOf H ∣ Nat.card (Hs i) := by
    have h1 := orderOf_dvd_natCard (⟨H, hH⟩ : ↥(Hs i))
    simpa [Subgroup.orderOf_coe] using h1
  intro x hx hconj
  obtain ⟨γ, hγ⟩ := isConj_iff.mp hconj
  set J : X := γ * H * γ⁻¹ with hJdef
  set K : X := γ * L * γ⁻¹ with hKdef
  have hxJK : x = J * K := by
    rw [← hγ]; simp only [hJdef, hKdef]; group
  have hJK : J * K = K * J := by
    have h1 : J * K = γ * (H * L) * γ⁻¹ := by simp only [hJdef, hKdef]; group
    have h2 : K * J = γ * (L * H) * γ⁻¹ := by simp only [hJdef, hKdef]; group
    rw [h1, h2, hcomm]
  have hordJ : orderOf J = orderOf H := by
    have hs : SemiconjBy γ H J := by
      change γ * H = J * γ
      rw [hJdef]; group
    exact hs.orderOf_eq.symm
  have hordK : orderOf K = orderOf L := by
    have hs : SemiconjBy γ L K := by
      change γ * L = K * γ
      rw [hKdef]; group
    exact hs.orderOf_eq.symm
  -- `orderOf J` and `orderOf K` are coprime
  have hcopJK : (orderOf J).Coprime (orderOf K) := by
    rw [hordK]
    exact Nat.Coprime.coprime_dvd_left (by rw [hordJ]; exact hHdvd) hcopL
  -- hence `|x| = |J| · |K|`
  have hord : orderOf x = orderOf J * orderOf K := by
    rw [hxJK]
    exact Commute.orderOf_mul_eq_mul_orderOf_of_coprime hJK hcopJK
  have hxdvd : orderOf J ∣ orderOf x := by
    rw [hord]; exact dvd_mul_right _ _
  -- conclude `|J| = 1`
  have hJ1 : orderOf J = 1 := by
    by_cases hx1 : x = 1
    · have h1 : orderOf J * orderOf K = 1 := by rw [← hord, hx1, orderOf_one]
      exact Nat.dvd_one.mp ⟨orderOf K, h1.symm⟩
    · have hcopJ : (orderOf J).Coprime (Nat.card (Hs i)) :=
        Nat.Coprime.coprime_dvd_left hxdvd (hcop x hx hx1).symm
      exact hcopJ.eq_one_of_dvd (by rw [hordJ]; exact hHdvd)
  exact hH1 (orderOf_eq_one_iff.mp (by rw [← hordJ]; exact hJ1))

end Work.Tame
