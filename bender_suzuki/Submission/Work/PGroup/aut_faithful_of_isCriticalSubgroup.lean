import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `p'`-automorphisms act faithfully on a Thompson critical subgroup

This file proves `Work.PGroup.aut_faithful_of_isCriticalSubgroup`: if `C` is a Thompson critical
subgroup of a finite `p`-group `P` and `A ≤ N_G(P)` is a `p'`-subgroup acting faithfully on `P`
(`A ⊓ C_G(P) = 1`), then `A` acts faithfully on `C` (`A ⊓ C_G(C) = 1`).  This is FT Lemma 8.2 (ii):
critical subgroups detect `p'`-automorphisms of `P`.

The mathematical content is the following elementary statement.  Let `a ∈ N_G(P)` centralize `C`
and have order coprime to `p`; we show that `a` centralizes `P`.

* By the Three Subgroups Lemma, applied to the subgroups `P`, `⟨a⟩` and `C`, the subgroup
  `[P, ⟨a⟩]` centralizes `C`.  Indeed `[⟨a⟩, C] = 1` because `a` fixes `C` pointwise, and
  `[C, P] ≤ Z(C)` with `a` fixing `Z(C) ⊆ C` pointwise.
* Since `C` is self-centralizing in `P`, this gives `[P, ⟨a⟩] ≤ C`.
* For `x ∈ P` put `u = [x⁻¹, a] = x⁻¹ · a x a⁻¹ ∈ [P, ⟨a⟩] ≤ C`.  As `a` centralizes `C`, we get
  `a u a⁻¹ = u`, and hence `a^i x a⁻¹^i = x u^i` by induction.  For `i = orderOf a` this yields
  `u ^ orderOf a = 1`.
* But `u ∈ P` is a `p`-element (order dividing `p ^ k` for some `k`), and `orderOf a` is coprime
  to `p`, so `orderOf u = 1`, i.e. `u = 1`.  Therefore `a x a⁻¹ = x` for every `x ∈ P`.
-/

set_option linter.unusedVariables false

open Subgroup
open scoped commutatorElement

namespace Work.PGroup

/-- **Faithfulness of `p'`-automorphisms on a critical subgroup, elementwise form.**
If `a ∈ N_G(P)` centralizes a critical subgroup `C` of the finite `p`-group `P` and `orderOf a` is
coprime to `p`, then `a` centralizes `P`. -/
theorem mem_centralizer_of_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P C : Subgroup G) [Finite P] (hP : IsPGroup p P) (hC : Work.PGroup.IsCriticalSubgroup p P C)
    {a : G} (haN : a ∈ Subgroup.normalizer (P : Set G))
    (hac : a ∈ Subgroup.centralizer (C : Set G)) (ha' : (orderOf a).Coprime p) :
    a ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  -- `u = [x⁻¹, a] = x⁻¹ · a x a⁻¹` lies in `P` and in `[P, ⟨a⟩]`.
  set u : G := ⁅x⁻¹, a⁆ with hu_def
  have huP : u ∈ P := by
    have h1 : a * x * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp haN x).mp hx
    have h2 : u = x⁻¹ * (a * x * a⁻¹) := by rw [hu_def, commutatorElement_def]; group
    rw [h2]; exact P.mul_mem (P.inv_mem hx) h1
  have hu_mem : u ∈ ⁅P, Subgroup.zpowers a⁆ := by
    rw [hu_def]
    exact Subgroup.commutator_mem_commutator (P.inv_mem hx) (Subgroup.mem_zpowers a)
  -- The Three Subgroups Lemma: `[[P, ⟨a⟩], C] = 1`.
  have hzpa : Subgroup.zpowers a ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.zpowers_le.mpr hac
  have h1 : ⁅⁅Subgroup.zpowers a, C⁆, P⁆ = ⊥ := by
    have hz : ⁅Subgroup.zpowers a, C⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hzpa
    rw [hz, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅C, P⁆, Subgroup.zpowers a⁆ = ⊥ := by
    have hCP : ⁅C, P⁆ ≤ Work.PGroup.centerIn C := by
      rw [Subgroup.commutator_comm]; exact hC.commutator_le_center
    have hZa : Subgroup.zpowers a ≤ Subgroup.centralizer (Work.PGroup.centerIn C : Set G) :=
      Subgroup.zpowers_le.mpr ((Subgroup.centralizer_le (Work.PGroup.centerIn_le C)) hac)
    have hZ : ⁅Subgroup.zpowers a, Work.PGroup.centerIn C⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZa
    have hZ' : ⁅Work.PGroup.centerIn C, Subgroup.zpowers a⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hZ
    exact le_bot_iff.mp (calc ⁅⁅C, P⁆, Subgroup.zpowers a⁆
        ≤ ⁅Work.PGroup.centerIn C, Subgroup.zpowers a⁆ :=
          Subgroup.commutator_mono hCP le_rfl
      _ = ⊥ := hZ')
  have hbot : ⁅⁅P, Subgroup.zpowers a⁆, C⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hle : ⁅P, Subgroup.zpowers a⁆ ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  -- Self-centralizing: `u ∈ C`.
  have huC : u ∈ C := hC.self_centralizing (Subgroup.mem_inf.mpr ⟨huP, hle hu_mem⟩)
  have hcomm_ua : u * a = a * u := Subgroup.mem_centralizer_iff.mp hac u huC
  have hau : a * u * a⁻¹ = u := by rw [← hcomm_ua]; group
  have hax : a * x * a⁻¹ = x * u := by rw [hu_def, commutatorElement_def]; group
  -- The orbit identity `a^i x a^{-i} = x u^i`, hence `u ^ orderOf a = 1`.
  have hstep : ∀ i : ℕ, a^i * x * (a^i)⁻¹ = x * u^i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc a^(i+1) * x * (a^(i+1))⁻¹
          = a * (a^i * x * (a^i)⁻¹) * a⁻¹ := by group
        _ = a * (x * u^i) * a⁻¹ := by rw [ih]
        _ = (a * x * a⁻¹) * (a * u^i * a⁻¹) := by group
        _ = (x * u) * u^i := by rw [hax, ← conj_pow, hau]
        _ = x * u^(i+1) := by group
  have hn := hstep (orderOf a)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hn
  have hun : u ^ (orderOf a) = 1 := by
    have h2 : x * u ^ (orderOf a) = x * 1 := by rw [mul_one]; exact hn.symm
    exact mul_left_cancel h2
  have hdvd_n : orderOf u ∣ orderOf a := orderOf_dvd_iff_pow_eq_one.mpr hun
  -- `u` is a `p`-element: `orderOf u ∣ p^k`.
  obtain ⟨k, hk⟩ := hP.exists_pow_pow_eq_one ⟨u, huP⟩
  have hk' : u ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd_p : orderOf u ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk'
  have hcop : (orderOf u).Coprime p := Nat.Coprime.coprime_dvd_left hdvd_n ha'
  have hd1 : orderOf u = 1 := by
    have hgcd : Nat.gcd (orderOf u) (p ^ k) = 1 := (hcop.pow_right k).gcd_eq_one
    have hdiv : orderOf u ∣ Nat.gcd (orderOf u) (p ^ k) := Nat.dvd_gcd dvd_rfl hdvd_p
    rw [hgcd] at hdiv
    exact Nat.dvd_one.mp hdiv
  have hu1 : u = 1 := orderOf_eq_one_iff.mp hd1
  calc x * a = (a * x * a⁻¹) * a := by rw [hax, hu1, mul_one]
    _ = a * x := by group

/-- **FT Lemma 8.2 (ii).**  A `p'`-subgroup `A ≤ N_G(P)` that acts faithfully on the finite
`p`-group `P` acts faithfully on any Thompson critical subgroup `C ≤ P`. -/
theorem aut_faithful_of_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P C : Subgroup G) [Finite P] (hP : IsPGroup p P) (hC : Work.PGroup.IsCriticalSubgroup p P C)
    (A : Subgroup G) (hA : A ≤ Subgroup.normalizer (P : Set G)) (hp'A : (Nat.card A).Coprime p)
    (hfaith : A ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    A ⊓ Subgroup.centralizer (C : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  obtain ⟨haA, hac⟩ := Subgroup.mem_inf.mp ha
  have hcard : (orderOf a).Coprime p :=
    Nat.Coprime.coprime_dvd_left (A.orderOf_dvd_natCard haA) hp'A
  have hcentP : a ∈ Subgroup.centralizer (P : Set G) :=
    mem_centralizer_of_isCriticalSubgroup hp P C hP hC (hA haA) hac hcard
  have : a ∈ A ⊓ Subgroup.centralizer (P : Set G) := Subgroup.mem_inf.mpr ⟨haA, hcentP⟩
  rw [hfaith] at this
  simpa using this

end Work.PGroup
