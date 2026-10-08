import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.conj_mem_hatNp_and_notMem
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.projEC_eq_self
import Submission.Work.Tame.alphaI2LM_apply_eq_card
import Submission.Work.Tame.conj_mul_notMem_Lhat
import Submission.Work.Tame.beta_eq_zero_of_notMem_hatNp
import Submission.Work.Tame.indFun_Lgrp_apply_of_mem_Lhat
import Submission.Work.Tame.indFun_eq_of_mem_hatNp
import Submission.Work.Tame.relIndex_eq_card_inf
import Submission.Work.Tame.alphaI1_isClassFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.tau_at_AL_v2` — Feit–Thompson Lemma 9.1, value part (p. 805)

If `L̂` is tamely imbedded in the finite group `X` with supporting subgroups `𝔎_1, …, 𝔎_n`, if
`α ∈ 𝓒₀(L̂)` and if `L ∈ 𝔏_j = LofIdx Lhat n Hs j` and `A ∈ 𝔄_L = ALofIdx Lhat n Hs j L`, then

`tau Lhat n Hs α A = α L`.

The proof expands `τ` as `α^* + Σ_i (α_{i1} − α_{i2})^*` and evaluates each summand.

* The first summand at `A ∈ L̂` is computed by `indFun_Lgrp_apply_of_mem_Lhat` as
  `|C(A)|·|C(A) ⊓ 𝔏|⁻¹·α A`; for `L ∈ 𝔏_i` the factor is `|C(L) ∩ 𝔎_i|` by (9.3), which is
  exactly the value of the `i`-th correction term (`alphaI2LM_apply_eq_card`), so that the two
  cancel; for `A ≠ L` the first summand vanishes by `conj_mul_notMem_Lhat`.
* The `i`-th correction term at `A ∈ Ñ_i^#` equals `β_i(A)` by `indFun_eq_of_mem_hatNp`, and for
  `j ≠ i` the `j`-th term vanishes because no conjugate of `A` lies in `Ñ_j^#`
  (`Lset_conj_hatNp` and its `𝔄_L`-analogue below).
* In the case `j = none` (`L ∈ 𝔏_0`, `A = L`) the first summand is `α L` and every correction
  term vanishes since no conjugate of `L ∈ 𝔏_0` lies in `Ñ_i^#`.

All the group-theoretic input is contained in Definition 9.1; the module builds on the lemmas
already established in this workspace (`conj_mul_notMem_Lhat`, `beta_eq_zero_of_notMem_hatNp`,
`indFun_Lgrp_apply_of_mem_Lhat`, `indFun_eq_of_mem_hatNp`).
-/

set_option maxHeartbeats 4000000

noncomputable section

open Classical
open scoped Pointwise

set_option maxHeartbeats 40000000
namespace Work.Tame

/-- The element `L` lies in its own centralizer, computed in the ambient group `X`. -/
private theorem self_mem_centralizer_X {X : Type*} [Group X] (L : X) :
    L ∈ Subgroup.centralizer ({L} : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy; rfl

variable {X : Type*} [Group X] [Fintype X]

/-- An element lies in its own centralizer. -/
theorem self_mem_centralizer {X : Type*} [Group X] (L : X) :
    L ∈ Subgroup.centralizer ({L} : Set X) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

/-- The cardinality of `H.subgroupOf K` is the cardinality of `H ⊓ K`. -/
theorem card_subgroupOf_eq_card_inf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective K),
    Subgroup.subgroupOf_map_subtype]

/-! ## (9.3): the decomposition of the centralizer of `L ∈ 𝔏_i` -/

/-- **Feit–Thompson (9.3)**, in the form used below: for `L ∈ 𝔏_i = Lset Lhat (Hs i)` the
centralizer of `L` is the product of its intersections with `𝔎_i` and `𝔏`. -/
theorem exists_eq_mul_of_mem_centralizer {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L : X}
    (hL : L ∈ Lset Lhat (Hs i)) {c : X} (hc : c ∈ Subgroup.centralizer ({L} : Set X)) :
    ∃ k ∈ Subgroup.centralizer ({L} : Set X) ⊓ Hs i,
      ∃ m ∈ Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat, c = k * m := by
  have hsup := h.supp_prod hne i
  have hinf := h.supp_inf hne i
  have hLhat : L ∈ Lhat := hL.1.1
  have hLmem : L ∈ Lgrp Lhat := h.sub_norm hLhat
  have hcent_le : Subgroup.centralizer ({L} : Set X) ≤ Lgrp (Hs i : Set X) := hL.2
  have hLself : L ∈ Subgroup.centralizer ({L} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hLmem' : L ∈ Lgrp (Hs i : Set X) := hcent_le hLself
  have hcN : c ∈ Lgrp (Hs i : Set X) := hcent_le hc
  set cN : ↥(Lgrp (Hs i : Set X)) := ⟨c, hcN⟩ with hcNdef
  set LN : ↥(Lgrp (Hs i : Set X)) := ⟨L, hLmem'⟩ with hLNdef
  have hconjc : cN * LN * cN⁻¹ = LN := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcNdef, hLNdef]
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hproj1 : projEC Lhat (Hs i) (cN * LN * cN⁻¹) = projEC Lhat (Hs i) LN := by rw [hconjc]
  rw [projEC_mul hsup hinf (cN * LN) cN⁻¹, projEC_mul hsup hinf cN LN] at hproj1
  have hprojL : projEC Lhat (Hs i) LN = ⟨L, hLmem, hLmem'⟩ := projEC_eq_self hinf ⟨L, hLmem, hLmem'⟩
  have hmcent : (projEC Lhat (Hs i) cN : X) ∈ Subgroup.centralizer ({L} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h9 : (projEC Lhat (Hs i) cN : X) * L * (projEC Lhat (Hs i) cN⁻¹ : X) = L := by
      rw [hprojL] at hproj1
      have h9' := congrArg (fun t : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) => (t : X)) hproj1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] using h9'
    have hinv : (projEC Lhat (Hs i) cN⁻¹ : X) = ((projEC Lhat (Hs i) cN : X))⁻¹ := by
      have h10 : projEC Lhat (Hs i) (cN * cN⁻¹) = projEC Lhat (Hs i) 1 := by rw [mul_inv_cancel]
      rw [projEC_mul hsup hinf, projEC_one hinf] at h10
      exact congrArg (fun t : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) => (t : X))
        (eq_inv_of_mul_eq_one_right h10)
    rw [hinv] at h9
    calc (projEC Lhat (Hs i) cN : X) * L
        = (projEC Lhat (Hs i) cN : X) * L * (projEC Lhat (Hs i) cN : X)⁻¹ *
            (projEC Lhat (Hs i) cN : X) := by group
      _ = L * (projEC Lhat (Hs i) cN : X) := by rw [h9]
  have hkmem : c * (projEC Lhat (Hs i) cN : X)⁻¹ ∈ Hs i := mul_projEC_inv_mem hsup cN
  have hkcent : c * (projEC Lhat (Hs i) cN : X)⁻¹ ∈ Subgroup.centralizer ({L} : Set X) :=
    (Subgroup.centralizer ({L} : Set X)).mul_mem hc
      ((Subgroup.centralizer ({L} : Set X)).inv_mem hmcent)
  exact ⟨c * (projEC Lhat (Hs i) cN : X)⁻¹, ⟨hkcent, hkmem⟩,
    (projEC Lhat (Hs i) cN : X), ⟨hmcent, (projEC Lhat (Hs i) cN).2.1⟩, by group⟩

/-- **Feit–Thompson (9.3)**: `|C(L)| = |C(L) ⊓ 𝔎_i| · |C(L) ⊓ 𝔏|` for `L ∈ 𝔏_i`. -/
theorem card_centralizer_eq_mul {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L : X}
    (hL : L ∈ Lset Lhat (Hs i)) :
    Nat.card ↥(Subgroup.centralizer ({L} : Set X)) =
      Nat.card ↥(Subgroup.centralizer ({L} : Set X) ⊓ Hs i) *
        Nat.card ↥(Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat) := by
  have hdisj : Disjoint (Subgroup.centralizer ({L} : Set X) ⊓ Hs i)
      (Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat) := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    have h1 : x ∈ Hs i ⊓ Lgrp Lhat := ⟨hx.2, hy.2⟩
    rw [h.supp_inf hne i] at h1
    simpa using h1
  let f : ↥(Subgroup.centralizer ({L} : Set X) ⊓ Hs i) ×
      ↥(Subgroup.centralizer ({L} : Set X) ⊓ Lgrp Lhat) →
      ↥(Subgroup.centralizer ({L} : Set X)) := fun p =>
    ⟨(p.1 : X) * (p.2 : X),
      Subgroup.mul_mem _ p.1.2.1 p.2.2.1⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have hval : (p.1 : X) * (p.2 : X) = (q.1 : X) * (q.2 : X) := by
      have := congrArg (fun t : ↥(Subgroup.centralizer ({L} : Set X)) => (t : X)) hpq
      simpa [f] using this
    exact Subgroup.mul_injective_of_disjoint hdisj hval
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨k, hk, m, hm, hkm⟩ := exists_eq_mul_of_mem_centralizer h hne hL c.2
    refine ⟨(⟨k, hk⟩, ⟨m, hm⟩), ?_⟩
    exact Subtype.ext hkm.symm
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

/-- **Feit–Thompson (9.3) + (ii)(a),(d)**: for `L ∈ 𝔏_i` and `j ≠ i` the number `|C(L)|` is
coprime to `|𝔎_j|`. -/
theorem coprime_card_Hs_centralizer {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i j : Fin n} (hij : j ≠ i)
    {L : X} (hL : L ∈ Lset Lhat (Hs i)) :
    (Nat.card (Hs j)).Coprime (Nat.card ↥(Subgroup.centralizer ({L} : Set X))) := by
  rw [card_centralizer_eq_mul h hne hL]
  refine Nat.Coprime.mul_right ?_ ?_
  · exact (h.supp_coprime hne j i hij).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  · have h2 := h.supp_coprime_cent hne j L hL.1.1 hL.1.2.1
    rwa [inf_comm] at h2


/-! ## Elements of `L̂` versus the T.I. sets `Ñ_i^#` -/

/-- No conjugate of an element `L ∈ 𝔏_0` (so `C(L) ⊆ 𝔏`) lies in `Ñ_i^#`: a non-identity
`H₀ ∈ 𝔎_i` commuting with `x L x⁻¹` would give an element `x⁻¹H₀x ∈ C(L) ⊆ 𝔏` whose order is
divisible by a prime of `|𝔎_i|`, contradicting Definition 9.1(ii)(d). -/
theorem not_isConj_mem_hatNp_of_mem_L0set {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L : X}
    (hL : L ∈ L0set Lhat) {x : X} : x * L * x⁻¹ ∉ hatNp (Hs i) := by
  intro hx
  obtain ⟨hxN, hxK, H₀, hH₀K, hH₀1, hcomm⟩ := mem_hatNp_iff.mp hx
  have hconj : x⁻¹ * H₀ * x ∈ Subgroup.centralizer ({L} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x⁻¹ * H₀ * x) * L = x⁻¹ * (H₀ * (x * L * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * L * x⁻¹) * H₀) * x := by rw [hcomm]
      _ = L * (x⁻¹ * H₀ * x) := by group
  have hcent : Subgroup.centralizer ({L} : Set X) ≤ Lgrp Lhat := (mem_L0set.mp hL).2.2
  have hmem : x⁻¹ * H₀ * x ∈ (Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X) : Subgroup X) :=
    ⟨hcent hconj, hconj⟩
  have hdvd : orderOf (x⁻¹ * H₀ * x) ∣
      Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hcop := h.supp_coprime_cent hne i L (mem_L0set.mp hL).1 (mem_L0set.mp hL).2.1
  have hdsem : SemiconjBy x⁻¹ H₀ (x⁻¹ * H₀ * x) := by
    show x⁻¹ * H₀ = (x⁻¹ * H₀ * x) * x⁻¹
    group
  have hord : orderOf H₀ = orderOf (x⁻¹ * H₀ * x) := SemiconjBy.orderOf_eq x⁻¹ hdsem
  have hHdvd : orderOf (x⁻¹ * H₀ * x) ∣ Nat.card (Hs i) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hH₀K
  have hone : orderOf (x⁻¹ * H₀ * x) = 1 := by
    refine Nat.dvd_one.mp ?_
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hHdvd hdvd
  exact hH₀1 (orderOf_eq_one_iff.mp (hord.trans hone))

/-- For `L ∈ 𝔏_i = Lset Lhat (Hs i)` and `j ≠ i`, no conjugate of `L` lies in `Ñ_j^#`: a witness
`H₀ ∈ 𝔎_j^#` commuting with `x L x⁻¹` gives `x⁻¹H₀x ∈ C(L)` with order dividing both `|𝔎_j|` and
`|C(L)|`, which are coprime by (9.3), (ii)(a) and (ii)(d). -/
theorem not_conj_mem_hatNp_of_mem_Lset {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i j : Fin n} (hij : j ≠ i)
    {L : X} (hL : L ∈ Lset Lhat (Hs i)) {x : X} : x * L * x⁻¹ ∉ hatNp (Hs j) := by
  intro hx
  obtain ⟨hxN, hxK, H₀, hH₀K, hH₀1, hcomm⟩ := mem_hatNp_iff.mp hx
  have hconj : x⁻¹ * H₀ * x ∈ Subgroup.centralizer ({L} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x⁻¹ * H₀ * x) * L = x⁻¹ * (H₀ * (x * L * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * L * x⁻¹) * H₀) * x := by rw [hcomm]
      _ = L * (x⁻¹ * H₀ * x) := by group
  have hdvdC : orderOf (x⁻¹ * H₀ * x) ∣ Nat.card ↥(Subgroup.centralizer ({L} : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ hconj
  have hdsem : SemiconjBy x⁻¹ H₀ (x⁻¹ * H₀ * x) := by
    show x⁻¹ * H₀ = (x⁻¹ * H₀ * x) * x⁻¹
    group
  have hord : orderOf H₀ = orderOf (x⁻¹ * H₀ * x) := SemiconjBy.orderOf_eq x⁻¹ hdsem
  have hHdvd : orderOf (x⁻¹ * H₀ * x) ∣ Nat.card (Hs j) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hH₀K
  have hone : orderOf (x⁻¹ * H₀ * x) = 1 := by
    refine Nat.dvd_one.mp ?_
    rw [← (coprime_card_Hs_centralizer h hne hij hL).gcd_eq_one]
    exact Nat.dvd_gcd hHdvd hdvdC
  exact hH₀1 (orderOf_eq_one_iff.mp (hord.trans hone))

/-- For `L ∈ 𝔏_i`: if some conjugate of `L` lies in `Ñ_i^#`, then `L ∈ Ñ_i^#`.  If `C_{𝔎_i}(L)`
were trivial then `C(L) = C_𝔏(L)` by (9.3), and the witness `x⁻¹H₀x ∈ C(L)` of order dividing
`|𝔎_i|` would have order dividing the coprime number `|C_𝔏(L)|`. -/
theorem mem_hatNp_of_conj_mem_hatNp_of_mem_Lset {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty)
    {i : Fin n} {L : X} (hL : L ∈ Lset Lhat (Hs i)) (hLhat : L ∈ Lhat) {x : X}
    (hx : x * L * x⁻¹ ∈ hatNp (Hs i)) : L ∈ hatNp (Hs i) := by
  have hinf := h.supp_inf hne i
  have hL1 : L ≠ 1 := hL.1.2.1
  have hLN : L ∈ Lgrp (Hs i : Set X) := hL.2 (self_mem_centralizer_X (L : X))
  have hLK : L ∉ Hs i := by
    intro hLK
    have h1 : L ∈ Hs i ⊓ Lgrp Lhat := ⟨hLK, h.sub_norm hLhat⟩
    rw [hinf] at h1
    exact hL1 (Subgroup.mem_bot.mp h1)
  rw [mem_hatNp_iff]
  refine ⟨hLN, hLK, ?_⟩
  by_contra hcon
  -- `C_{𝔎_i}(L) = 1`, hence `C(L) = C_𝔏(L)` by (9.3)
  obtain ⟨hxN, hxK, H₀, hH₀K, hH₀1, hcomm⟩ := mem_hatNp_iff.mp hx
  have hconj : x⁻¹ * H₀ * x ∈ Subgroup.centralizer ({L} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x⁻¹ * H₀ * x) * L = x⁻¹ * (H₀ * (x * L * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * L * x⁻¹) * H₀) * x := by rw [hcomm]
      _ = L * (x⁻¹ * H₀ * x) := by group
  -- the elementwise decomposition (9.3) together with `C_{𝔎_i}(L) = 1`
  obtain ⟨k, hk, m, hm, hkm⟩ := exists_eq_mul_of_mem_centralizer h hne hL hconj
  have hkCL : k ∈ Subgroup.centralizer ({L} : Set X) := hk.1
  have hkCL' : k * L = L * k := Subgroup.mem_centralizer_singleton_iff.mp hkCL
  have hk1 : k = 1 := by
    by_contra hkne
    exact hcon ⟨k, hk.2, hkne, hkCL'.symm⟩
  have hxH : x⁻¹ * H₀ * x = m := by rw [hkm, hk1, one_mul]
  have hmem : x⁻¹ * H₀ * x ∈ (Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X) : Subgroup X) := by
    rw [hxH]
    exact ⟨hm.2, hm.1⟩
  have hdvd : orderOf (x⁻¹ * H₀ * x) ∣
      Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({L} : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hcop := h.supp_coprime_cent hne i L hLhat hL1
  have hdsem : SemiconjBy x⁻¹ H₀ (x⁻¹ * H₀ * x) := by
    show x⁻¹ * H₀ = (x⁻¹ * H₀ * x) * x⁻¹
    group
  have hord : orderOf H₀ = orderOf (x⁻¹ * H₀ * x) := SemiconjBy.orderOf_eq x⁻¹ hdsem
  have hHdvd : orderOf (x⁻¹ * H₀ * x) ∣ Nat.card (Hs i) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hH₀K
  have hone : orderOf (x⁻¹ * H₀ * x) = 1 := by
    refine Nat.dvd_one.mp ?_
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hHdvd hdvd
  exact hH₀1 (orderOf_eq_one_iff.mp (hord.trans hone))

/-! ## The remaining group theory -/

/-- For `L ∈ 𝔏_i` and `H ∈ 𝔎_i`, the orders of `H` and `L` are coprime (Definition 9.1(ii)(b)
makes `𝔎_i` a Hall subgroup of `𝔑_i`, and `L ∈ 𝔏 ⊓ 𝔑_i`). -/
theorem coprime_orderOf_of_mem_Lset_mem_Hs {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) :
    (orderOf H).Coprime (orderOf L) := by
  have hdvdK : orderOf H ∣ Nat.card (Hs i) := Subgroup.orderOf_dvd_natCard _ hH
  have hLN : L ∈ Lgrp (Hs i : Set X) := hL.2 (self_mem_centralizer_X (L : X))
  have hmem : L ∈ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X) : Subgroup X) := ⟨h.sub_norm hL.1.1, hLN⟩
  have hdvdM : orderOf L ∣ Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hcop : (Nat.card (Hs i)).Coprime
      (Nat.card ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X))) := by
    rw [← relIndex_eq_card_inf h hne i]
    exact (h.supp_hall hne i).2
  exact (hcop.coprime_dvd_left hdvdK).coprime_dvd_right hdvdM

open scoped Classical in
/-- For commuting elements of coprime order, anything commuting with `x * y` commutes with `x`
(`x` is a power of `x * y` by the Chinese remainder theorem). -/
theorem centralizer_mul_le_of_coprime_order {G : Type*} [Group G] {x y : G} (hcomm : Commute x y)
    (hcop : (orderOf x).Coprime (orderOf y)) :
    Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  obtain ⟨s, hs1, hs0⟩ := Nat.chineseRemainder hcop 1 0
  have hxs : x ^ s = x := by
    have h1 : s % orderOf x = 1 % orderOf x := hs1
    rw [← pow_mod_orderOf (x := x) (n := s), h1, pow_mod_orderOf]
    exact pow_one x
  have hys : y ^ s = 1 := by
    have h0 : s % orderOf y = 0 := hs0
    rw [← pow_mod_orderOf (x := y) (n := s), h0, pow_zero]
  have hxy : (x * y) ^ s = x := by
    rw [Commute.mul_pow hcomm, hxs, hys, mul_one]
  have hc' : Commute c (x * y) := hc
  calc c * x = c * (x * y) ^ s := by rw [hxy]
    _ = (x * y) ^ s * c := (hc'.pow_right s).eq
    _ = x * c := by rw [hxy]

/-- The element `L * H` of Feit–Thompson's `𝔄_L` lies in `Ñ_i^#` when `H ∈ 𝔎_i^#` commutes with
`L ∈ 𝔏_i`. -/
theorem mem_hatNp_of_mem_AL {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n} {L H : X}
    (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) (hH1 : H ≠ 1) (hcomm : H * L = L * H) :
    L * H ∈ hatNp (Hs i) := by
  have hLhat : L ∈ Lhat := hL.1.1
  have hL1 : L ≠ 1 := hL.1.2.1
  have hLN : L ∈ Lgrp (Hs i : Set X) := hL.2 (self_mem_centralizer_X (L : X))
  have hsup := h.supp_prod hne i
  have hinf := h.supp_inf hne i
  have hHN : H ∈ Lgrp (Hs i : Set X) := Subgroup.le_normalizer hH
  have hLHN : L * H ∈ Lgrp (Hs i : Set X) := (Lgrp (Hs i : Set X)).mul_mem hLN hHN
  have hcomm' : (L * H) * H = H * (L * H) := by
    rw [show (L * H) * H = L * (H * H) from by group,
      show H * (L * H) = (H * L) * H from by group, hcomm]
    group
  rw [mem_hatNp_iff]
  refine ⟨hLHN, ?_, H, hH, hH1, hcomm'⟩
  intro hmem
  have hHone : projEC Lhat (Hs i) ⟨H, hHN⟩ = 1 :=
    projEC_eq_of hinf (N := ⟨H, hHN⟩) (m := 1) (by simpa using hH)
  have h1 : projEC Lhat (Hs i) ⟨L * H, hLHN⟩ = projEC Lhat (Hs i) ⟨L, hLN⟩ := by
    rw [show (⟨L * H, hLHN⟩ : ↥(Lgrp (Hs i : Set X))) = ⟨L, hLN⟩ * ⟨H, hHN⟩ from Subtype.ext rfl,
      projEC_mul hsup hinf, hHone, mul_one]
  have h2 : projEC Lhat (Hs i) ⟨L * H, hLHN⟩ = 1 :=
    projEC_eq_of hinf (m := (1 : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)))) (by simpa using hmem)
  have h3 : projEC Lhat (Hs i) ⟨L, hLN⟩ = ⟨L, h.sub_norm hLhat, hLN⟩ :=
    projEC_eq_self hinf ⟨L, h.sub_norm hLhat, hLN⟩
  rw [h2, h3] at h1
  exact hL1 (congrArg (fun t : ↥(Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) => (t : X)) h1).symm

/-- For `L ∈ 𝔏_i` and `H ∈ 𝔎_i^#` commuting with `L`, no conjugate of `L * H` lies in `Ñ_j^#`
for `j ≠ i`; indeed `x⁻¹K₀x ∈ C(L*H) ⊆ C(L)` would have order dividing both `|𝔎_j|` and
`|C(L)|`, which are coprime. -/
theorem not_conj_mem_hatNp_of_mem_AL {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i j : Fin n} (hij : j ≠ i)
    {L H : X} (hL : L ∈ Lset Lhat (Hs i)) (hH : H ∈ Hs i) (hH1 : H ≠ 1)
    (hcomm : H * L = L * H) {x : X} : x * (L * H) * x⁻¹ ∉ hatNp (Hs j) := by
  intro hx
  obtain ⟨hxN, hxK, K₀, hK₀K, hK₀1, hcomm₀⟩ := mem_hatNp_iff.mp hx
  have hconj : x⁻¹ * K₀ * x ∈ Subgroup.centralizer ({L * H} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x⁻¹ * K₀ * x) * (L * H) = x⁻¹ * (K₀ * (x * (L * H) * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * (L * H) * x⁻¹) * K₀) * x := by rw [hcomm₀]
      _ = (L * H) * (x⁻¹ * K₀ * x) := by group
  have hcommLH : Commute L H := hcomm.symm
  have hcop : (orderOf L).Coprime (orderOf H) :=
    (coprime_orderOf_of_mem_Lset_mem_Hs h hne hL hH).symm
  have hle := centralizer_mul_le_of_coprime_order hcommLH hcop
  have hdvdC : orderOf (x⁻¹ * K₀ * x) ∣ Nat.card ↥(Subgroup.centralizer ({L} : Set X)) :=
    Subgroup.orderOf_dvd_natCard _ (hle hconj)
  have hdsem : SemiconjBy x⁻¹ K₀ (x⁻¹ * K₀ * x) := by
    show x⁻¹ * K₀ = (x⁻¹ * K₀ * x) * x⁻¹
    group
  have hord : orderOf K₀ = orderOf (x⁻¹ * K₀ * x) := SemiconjBy.orderOf_eq x⁻¹ hdsem
  have hHdvd : orderOf (x⁻¹ * K₀ * x) ∣ Nat.card (Hs j) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hK₀K
  have hone : orderOf (x⁻¹ * K₀ * x) = 1 := by
    refine Nat.dvd_one.mp ?_
    rw [← (coprime_card_Hs_centralizer h hne hij hL).gcd_eq_one]
    exact Nat.dvd_gcd hHdvd hdvdC
  exact hK₀1 (orderOf_eq_one_iff.mp (hord.trans hone))

/-! ## Auxiliary facts about the correction term `β_i = α_{i1} − α_{i2}` -/

/-- `β_i` is a class function of `𝔑_i`. -/
theorem isClassFun_beta {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) (i : Fin n) :
    CharCore.IsClassFun (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) :=
  (alphaI1_isClassFun (h.supp_prod hne i) (h.supp_inf hne i) hα.1).sub
    (Work.Induction.isClassFun_indFun _ _)

/-- **The `i`-th correction term at an element of `Ñ_i^#`** is the value of `β_i` itself. -/
theorem indFun_beta_apply_of_mem_hatNp {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) (i : Fin n) {N : ↥(Lgrp (Hs i : Set X))}
    (hN : (N : X) ∈ hatNp (Hs i)) :
    Induction.indFun (Lgrp (Hs i : Set X))
      (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) (N : X) =
      (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) N :=
  indFun_eq_of_mem_hatNp h hne i (isClassFun_beta h hne hα i)
    (fun N hN => beta_eq_zero_of_notMem_hatNp h hne hα i hN) hN

/-- A correction term vanishes at `g` when no conjugate of `g` lies in `Ñ_i^#`. -/
theorem indFun_beta_eq_zero_of_forall_not_conj {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) (i : Fin n) {g : X}
    (hconj : ∀ x : X, x * g * x⁻¹ ∉ hatNp (Hs i)) :
    Induction.indFun (Lgrp (Hs i : Set X))
      (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) g = 0 := by
  rw [Induction.indFun_apply_def, mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x * g * x⁻¹ ∈ Lgrp (Hs i : Set X)
  · rw [dif_pos hx]
    exact beta_eq_zero_of_notMem_hatNp h hne hα i (hconj x)
  · rw [dif_neg hx]

/-! ## The values of `α_{i1}`, `α_{i2}` and `β_i` at `L ∈ 𝔏_i` -/

/-- `α_{i1}(L) = α(L)` for `L ∈ 𝔏_i`. -/
theorem alphaI1_apply_self {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n}
    {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ Lset Lhat (Hs i)) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) :
    alphaI1LM Lhat (Hs i) α
      ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ = α L := by
  have hinf := h.supp_inf hne i
  have hproj : projEC Lhat (Hs i)
      ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ =
      ⟨(L : X), h.sub_norm hL.1.1, hL.2 (self_mem_centralizer_X (L : X))⟩ :=
    projEC_eq_self hinf ⟨(L : X), h.sub_norm hL.1.1,
      hL.2 (self_mem_centralizer_X (L : X))⟩
  rw [alphaI1LM_apply, hproj]
  rfl

/-- `α_{i2}(L) = |C(L) ⊓ 𝔎_i|·α(L)` for `L ∈ 𝔏_i` (Feit–Thompson (9.5)). -/
theorem alphaI2_apply_self {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n}
    {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ Lset Lhat (Hs i)) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) :
    alphaI2LM Lhat (Hs i) α
      ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ =
      (Nat.card ↥(Subgroup.centralizer ({(L : X)} : Set X) ⊓ Hs i) : ℂ) * α L := by
  have hsup := h.supp_prod hne i
  have hinf := h.supp_inf hne i
  have hLN : (L : X) ∈ Lgrp (Hs i : Set X) :=
    hL.2 (self_mem_centralizer_X (L : X))
  have hproj : projEC Lhat (Hs i) ⟨(L : X), hLN⟩ = ⟨(L : X), h.sub_norm hL.1.1, hLN⟩ :=
    projEC_eq_self hinf ⟨(L : X), h.sub_norm hL.1.1, hLN⟩
  rw [alphaI2LM_apply_eq_card_gen hsup hinf hα ⟨(L : X), hLN⟩, hproj]
  have hcard : Nat.card {k : ↥(Hs i) // (k : X)⁻¹ * (L : X) * (k : X) = (L : X)} =
      Nat.card ↥(Subgroup.centralizer ({(L : X)} : Set X) ⊓ Hs i) := by
    rw [← card_subgroupOf_eq_card_inf (Subgroup.centralizer ({(L : X)} : Set X)) (Hs i)]
    refine Nat.card_congr ?_
    exact Equiv.subtypeEquivRight (fun k => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hk
        calc (k : X) * (L : X) = (k : X) * ((k : X)⁻¹ * (L : X) * (k : X)) := by rw [hk]
          _ = (L : X) * (k : X) := by group
      · intro hk
        calc (k : X)⁻¹ * (L : X) * (k : X) = (k : X)⁻¹ * ((L : X) * (k : X)) := by group
          _ = (k : X)⁻¹ * ((k : X) * (L : X)) := by rw [← hk]
          _ = (L : X) := by group)
  rw [hcard]
  rfl

/-- `β_i(L) = α(L) − |C(L) ⊓ 𝔎_i|·α(L)` for `L ∈ 𝔏_i`. -/
theorem beta_apply_self {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n}
    {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ Lset Lhat (Hs i)) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) :
    (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α)
        ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ =
      α L - (Nat.card ↥(Subgroup.centralizer ({(L : X)} : Set X) ⊓ Hs i) : ℂ) * α L := by
  have h1 := alphaI1_apply_self h hne hL hα
  have h2 := alphaI2_apply_self h hne hL hα
  show alphaI1LM Lhat (Hs i) α ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ -
      alphaI2LM Lhat (Hs i) α ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ = _
  rw [h1, h2]

/-- The `i`-th correction term at `L ∈ 𝔏_i` equals `β_i(L)`. -/
theorem indFun_beta_apply_self {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i : Fin n}
    {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ Lset Lhat (Hs i)) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) :
    Induction.indFun (Lgrp (Hs i : Set X))
        (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) (L : X) =
      (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α)
        ⟨(L : X), hL.2 (self_mem_centralizer_X (L : X))⟩ := by
  have hLN : (L : X) ∈ Lgrp (Hs i : Set X) :=
    hL.2 (self_mem_centralizer_X (L : X))
  by_cases hLi : (L : X) ∈ hatNp (Hs i)
  · exact indFun_beta_apply_of_mem_hatNp (N := ⟨(L : X), hLN⟩) h hne hα i hLi
  · rw [indFun_beta_eq_zero_of_forall_not_conj h hne hα i
      (fun x hx => hLi (mem_hatNp_of_conj_mem_hatNp_of_mem_Lset h hne hL hL.1.1 hx))]
    exact (beta_eq_zero_of_notMem_hatNp h hne hα i hLi).symm

/-- The `j`-th correction term at `L ∈ 𝔏_i` vanishes for `j ≠ i`. -/
theorem indFun_beta_apply_self_eq_zero {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) {i j : Fin n} (hij : j ≠ i)
    {L : ↥(Lgrp Lhat)} (hL : (L : X) ∈ Lset Lhat (Hs i)) {α : ↥(Lgrp Lhat) → ℂ}
    (hα : α ∈ C0 Lhat) :
    Induction.indFun (Lgrp (Hs j : Set X))
      (alphaI1LM Lhat (Hs j) α - alphaI2LM Lhat (Hs j) α) (L : X) = 0 :=
  indFun_beta_eq_zero_of_forall_not_conj h hne hα j
    (fun x => not_conj_mem_hatNp_of_mem_Lset h hne hij hL)

end Work.Tame
