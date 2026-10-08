import Mathlib
import Submission.Work.PSTAB.Prelude

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped commutatorElement
open Subgroup

namespace Work.PSTAB

/-- The set of elements of `M` acting trivially on the `i`-th chief factor of the chief
series of `K` is a subgroup of `M`.

Membership is stated element-wise, which is what makes the closure lemmas below
elementary; the equivalence with `⁅chiefSeriesInside K i, Subgroup.zpowers g⁆ ≤ …` used
in the hypothesis of `StabQuotientPGroup` is immediate from
`Subgroup.commutator_le`. -/
private def stabFactor {M : Type*} [Group M] [Finite M] (K : Subgroup M) [K.Normal]
    (i : ℕ) : Subgroup M where
  carrier := {g : M | ∀ x ∈ OddOrder.GroupTheory.chiefSeriesInside K i,
      ⁅x, g⁆ ∈ OddOrder.GroupTheory.chiefSeriesInside K (i + 1)}
  one_mem' := by
    intro x _hx
    simp
  mul_mem' := by
    intro a b ha hb x hx
    have hB : (OddOrder.GroupTheory.chiefSeriesInside K (i + 1)).Normal :=
      OddOrder.GroupTheory.chiefSeriesInside_instNormal K (i + 1)
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) by group]
    exact (OddOrder.GroupTheory.chiefSeriesInside K (i + 1)).mul_mem (ha x hx)
      (hB.conj_mem ⁅x, b⁆ (hb x hx) a)
  inv_mem' := by
    intro a ha x hx
    have hB : (OddOrder.GroupTheory.chiefSeriesInside K (i + 1)).Normal :=
      OddOrder.GroupTheory.chiefSeriesInside_instNormal K (i + 1)
    have hmem : ⁅a, x⁆ ∈ OddOrder.GroupTheory.chiefSeriesInside K (i + 1) :=
      commutatorElement_inv x a ▸
        (OddOrder.GroupTheory.chiefSeriesInside K (i + 1)).inv_mem (ha x hx)
    rw [commutatorElement_inv_right]
    simpa [inv_inv] using hB.conj_mem ⁅a, x⁆ hmem a⁻¹

/-- Every `p'`-subgroup of `H` centralizes the normal `p`-subgroup `K`.

This is BG Lemma 1.9 applied to the subgroup in question: the hypothesis of
`StabQuotientPGroup` says that every element of `H` acts trivially on every chief factor
of `K`, hence so does every subgroup of `H`; a subgroup of order coprime to `p` that
stabilises every factor of the chief series centralizes `K`. -/
private theorem sub_le_centralizer_of_coprime {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] {K : Subgroup M} [K.Normal] (hK : IsPGroup p K) (H : Subgroup M)
    (hstab : ∀ h ∈ H, ∀ i : ℕ,
      ⁅OddOrder.GroupTheory.chiefSeriesInside K i, Subgroup.zpowers h⁆ ≤
        OddOrder.GroupTheory.chiefSeriesInside K (i + 1))
    {D : Subgroup M} (hDH : D ≤ H) (hD : (Nat.card ↥D).Coprime p) :
    D ≤ Subgroup.centralizer (K : Set M) := by
  have hHstab : ∀ i, H ≤ stabFactor K i := by
    intro i h hh x hx
    exact (Subgroup.commutator_le.mp (hstab h hh i)) x hx h (Subgroup.mem_zpowers h)
  refine OddOrder.BG.Ch2.S09.coprime_chiefSeries_stabilizer_le_centralizer ?_ ?_ ?_
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
    rw [hn]
    exact hD.pow_right n
  · have hnil : Group.IsNilpotent ↥K := IsPGroup.isNilpotent hK
    haveI : Group.IsNilpotent ↥K := hnil
    exact Or.inr inferInstance
  · intro i
    exact Subgroup.commutator_le.mpr
      (fun x hx y hy => (hHstab i (hDH hy)) x hx)

theorem StabQuotientPGroup {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K) (H : Subgroup M)
    (hstab : ∀ h ∈ H, ∀ i : ℕ, ⁅OddOrder.GroupTheory.chiefSeriesInside K i, Subgroup.zpowers h⁆ ≤
      OddOrder.GroupTheory.chiefSeriesInside K (i + 1)) :
    IsPGroup p (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))) := by
  set φ := QuotientGroup.mk' (Subgroup.centralizer (K : Set M)) with hφ
  set J := H.map φ with hJ
  have hker : φ.ker = Subgroup.centralizer (K : Set M) := QuotientGroup.ker_mk' _
  have hreli : (Subgroup.centralizer (K : Set M)).relIndex H = Nat.card ↥J := by
    have h := Subgroup.relIndex_ker H φ
    rw [hker, ← hJ] at h
    exact h
  -- the cardinal identity `|J| * |H ⊓ C_M(K)| = |H|`
  have hcard : Nat.card ↥J * Nat.card ↥(H ⊓ Subgroup.centralizer (K : Set M)) = Nat.card ↥H := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (K : Set M)) H
    rw [hreli, inf_comm] at h1
    exact h1
  have hJne : Nat.card ↥J ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨1, J.one_mem⟩⟩, inferInstance⟩
  refine IsPGroup.iff_card.mpr ⟨(Nat.card ↥J).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd hJne ?_
  intro d hd hdvd
  by_contra hdp
  -- `d` is a prime `≠ p` dividing `|J|`; a Sylow `d`-subgroup of `H` would have to
  -- centralize `K`, which is impossible.
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := d) (G := ↥H)
  set Q : Subgroup ↥H := (P : Subgroup ↥H) with hQ
  have hDcop : (Nat.card ↥(Q.map H.subtype)).Coprime p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hk]
    exact (Nat.coprime_primes hd (inferInstance : Fact p.Prime).out).mpr hdp |>.pow_left k
  have hDcent : Q.map H.subtype ≤ Subgroup.centralizer (K : Set M) :=
    sub_le_centralizer_of_coprime hK H hstab (Subgroup.map_subtype_le Q) hDcop
  have hDleC : Q.map H.subtype ≤ H ⊓ Subgroup.centralizer (K : Set M) :=
    le_inf (Subgroup.map_subtype_le Q) hDcent
  have hPdvd : Nat.card ↥Q ∣ Nat.card ↥(H ⊓ Subgroup.centralizer (K : Set M)) := by
    have h := Subgroup.card_dvd_of_le hDleC
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h
  have hQindex : ¬ d ∣ Q.index := Sylow.not_dvd_index P
  obtain ⟨t, ht⟩ := hPdvd
  have hEq : Nat.card ↥Q * Q.index = Nat.card ↥Q * (Nat.card ↥J * t) := by
    rw [Subgroup.card_mul_index Q, ← hcard, ht]
    ring
  have hidx : Q.index = Nat.card ↥J * t := Nat.mul_left_cancel Nat.card_pos hEq
  exact hQindex (hidx ▸ dvd_mul_of_dvd_left hdvd t)

end Work.PSTAB
