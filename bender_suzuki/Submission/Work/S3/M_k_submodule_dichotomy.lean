import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.S3.ConjRep
import Submission.Work.ThmF.Prove.S3.clifford_dichotomy
import Submission.Work.ThmF.ChV12.prop3_frobenius_power
import Submission.Work.S3.EllCorrDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.S3

open scoped IsMulCommutative

/-- The subgroup `L = K ⊔ P` normalizes the subgroup `M` of the statement: conjugation by any of
its elements preserves `M` (`hMinv`). -/
theorem le_normalizer_of_conj_mem {G : Type} [Group G] {K P M : Subgroup G}
    (hMinv : ∀ x ∈ (K ⊔ P), ∀ m ∈ M, x * m * x⁻¹ ∈ M) :
    (K ⊔ P) ≤ Subgroup.normalizer (M : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · exact hMinv x hx m
  · intro hm
    have h1 : x⁻¹ * (x * m * x⁻¹) * (x⁻¹)⁻¹ ∈ M :=
      hMinv x⁻¹ ((K ⊔ P).inv_mem hx) _ hm
    have h2 : x⁻¹ * (x * m * x⁻¹) * (x⁻¹)⁻¹ = m := by group
    rwa [h2] at h1

/-- A `ZMod n`-submodule `W ≤ Additive ↥M` is invariant under the conjugation action of `k : ↥L`
if and only if the corresponding subgroup `subOfSubmodule M W ≤ G` is normalised by `(k : G)`. -/
theorem conjRepOfLe_mem_subOfSubmodule_iff {G : Type} [Group G] {M L : Subgroup G}
    (hLN : L ≤ Subgroup.normalizer (M : Set G)) [IsMulCommutative ↥M] {n : ℕ}
    [Fact (∀ x : ↥M, x ^ n = 1)] (k : ↥L) (W : Submodule (ZMod n) (Additive ↥M)) :
    (∀ w ∈ W, Work.ThmF.Prove.S3.conjRepOfLe (n := n) L M hLN k w ∈ W) ↔
      (∀ u ∈ subOfSubmodule M W,
        (k : G) * u * (k : G)⁻¹ ∈ subOfSubmodule M W) := by
  constructor
  · intro h u hu
    obtain ⟨huM, huW⟩ := (subOfSubmodule_mem M W u).mp hu
    have h1 := h _ huW
    rw [Work.ThmF.Prove.S3.conjRepOfLe_apply] at h1
    exact ⟨((hLN k.2) (⟨u, huM⟩ : ↥M)).mp huM, h1⟩
  · intro h w hw
    have h1 : ((Additive.toMul w : ↥M) : G) ∈ subOfSubmodule M W :=
      (ofMul_mem_subOfSubmodule M W (Additive.toMul w)).mp hw
    obtain ⟨h1M, h1W⟩ := (subOfSubmodule_mem M W _).mp h1
    have h2 := h _ ⟨h1M, h1W⟩
    obtain ⟨h2M, h2W⟩ := (subOfSubmodule_mem M W _).mp h2
    rw [show w = Additive.ofMul (Additive.toMul w) from rfl,
      Work.ThmF.Prove.S3.conjRepOfLe_apply]
    exact h2W

theorem M_k_submodule_dichotomy {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t))
    (hKlcop : ¬ ℓ ∣ Nat.card ↥(Work.ThmF.Ksub H t))
    (hKP : P ⊓ Work.ThmF.Ksub H t = ⊥)
    {M : Subgroup G} (hMne : M ≠ ⊥) (hMcomm : IsMulCommutative ↥M)
    (hMexp : ∀ x : ↥M, x ^ ℓ = 1)
    (hMinv : ∀ x ∈ (Work.ThmF.Ksub H t ⊔ P), ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hMcard : Nat.card ↥M = ℓ ^ Nat.card P)
    (hMirr : ∀ N : Subgroup G, N ≤ M → N ≠ ⊥ →
      (∀ x ∈ (Work.ThmF.Ksub H t ⊔ P), ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N = M) :
    (∃ U : Subgroup G, U ≤ M ∧ U ≠ ⊥ ∧ Nat.card ↥U = ℓ ∧
        (∀ k ∈ Work.ThmF.Ksub H t, ∀ u ∈ U, k * u * k⁻¹ ∈ U))
      ∨ (∀ N : Subgroup G, N ≤ M → N ≠ ⊥ →
        (∀ k ∈ Work.ThmF.Ksub H t, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → N = M) := by
  classical
  haveI hfact : Fact (∀ x : ↥M, x ^ ℓ = 1) := ⟨hMexp⟩
  haveI hprime : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hMfin : Fintype ↥M := Fintype.ofFinite _
  haveI hLfin : Fintype ↥(Work.ThmF.Ksub H t ⊔ P) := Fintype.ofFinite _
  haveI hDfin : FiniteDimensional (ZMod ℓ) (Additive ↥M) :=
    Module.Finite.of_finite (R := ZMod ℓ) (M := Additive ↥M)
  -- the normalizer hypothesis
  have hLN : (Work.ThmF.Ksub H t ⊔ P) ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_of_conj_mem hMinv
  -- the group-theoretic setup for `K ⊔ P`
  have hPN : P ≤ Subgroup.normalizer (Work.ThmF.Ksub H t : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Work.ThmF.ChV12.conj_mem_Ksub H t (c.P_le hp) y hy
    · intro hy
      have h1 := Work.ThmF.ChV12.conj_mem_Ksub H t
        ((Submission.Blueprint.centD H t).inv_mem (c.P_le hp)) (p * y * p⁻¹) hy
      have h2 : p⁻¹ * (p * y * p⁻¹) * (p⁻¹)⁻¹ = y := by group
      rwa [h2] at h1
  have hKn : ((Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P)).Normal := by
    have h := Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (H := P) (N := Work.ThmF.Ksub H t) hPN
    rwa [sup_comm] at h
  have hinf : (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P) ⊓
      P.subgroupOf (Work.ThmF.Ksub H t ⊔ P) = ⊥ := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : (x : G) ∈ P ⊓ Work.ThmF.Ksub H t := ⟨h2, h1⟩
      rw [hKP] at h3
      exact Subtype.ext (Subgroup.mem_bot.mp h3)
    · intro h
      rw [h]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hsup : (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P) ⊔
      P.subgroupOf (Work.ThmF.Ksub H t ⊔ P) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := Work.ThmF.Ksub H t) (A' := P)
      (B := Work.ThmF.Ksub H t ⊔ P) le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hKcard : Nat.card ↥((Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P)) =
      Nat.card ↥(Work.ThmF.Ksub H t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Work.ThmF.Ksub H t)
      (K := Work.ThmF.Ksub H t ⊔ P) le_sup_left).toEquiv
  have hEcard : Nat.card ↥(P.subgroupOf (Work.ThmF.Ksub H t ⊔ P)) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P)
      (K := Work.ThmF.Ksub H t ⊔ P) le_sup_right).toEquiv
  -- the dimension of `M` as a `ZMod ℓ`-module
  have hV : Module.finrank (ZMod ℓ) (Additive ↥M) = Nat.card P := by
    haveI : Fintype (Additive ↥M) := Fintype.ofFinite _
    have hfr := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := Additive ↥M)
    rw [ZMod.card] at hfr
    have h1 : ℓ ^ Module.finrank (ZMod ℓ) (Additive ↥M) = ℓ ^ Nat.card P := by
      rw [← hfr, ← Nat.card_eq_fintype_card]
      exact hMcard
    exact Nat.pow_right_injective hℓ.two_le h1
  -- the characteristic hypothesis
  have hchar : ∀ q : ℕ, q.Prime → (q : ZMod ℓ) = 0 →
      ¬ q ∣ Nat.card ↥((Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P)) := by
    intro q hq hq0
    have hdvd : ℓ ∣ q := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ q).mp hq0
    have hqeq : q = ℓ := ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp hdvd).symm
    rw [hqeq, hKcard]
    exact hKlcop
  -- irreducibility of `M` as a module over `K ⊔ P`
  have hirr : ∀ W : Submodule (ZMod ℓ) (Additive ↥M),
      (∀ l : ↥(Work.ThmF.Ksub H t ⊔ P), ∀ w ∈ W,
        Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) (Work.ThmF.Ksub H t ⊔ P) M hLN l w ∈ W) →
      W ≠ ⊥ → W = ⊤ := by
    intro W hWinv hWne
    have hSle : subOfSubmodule M W ≤ M := subOfSubmodule_le M W
    have hSne : subOfSubmodule M W ≠ ⊥ :=
      fun h => hWne ((subOfSubmodule_eq_bot_iff M W).mp h)
    have hSinv : ∀ x ∈ (Work.ThmF.Ksub H t ⊔ P), ∀ n ∈ subOfSubmodule M W,
        x * n * x⁻¹ ∈ subOfSubmodule M W := by
      intro x hx n hn
      exact (conjRepOfLe_mem_subOfSubmodule_iff (n := ℓ) hLN ⟨x, hx⟩ W).mp
        (hWinv ⟨x, hx⟩) n hn
    exact (subOfSubmodule_eq_M_iff M W).mp
      (hMirr (subOfSubmodule M W) hSle hSne hSinv)
  obtain ⟨U, hUne, hUinv, hUfr⟩ | hKsim :=
    Work.ThmF.Prove.S3.clifford_dichotomy hKn hinf hsup c.P_prime hEcard hchar (V := Additive ↥M) hV
      (Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) (Work.ThmF.Ksub H t ⊔ P) M hLN) hirr
  · -- Case 1: there is a one-dimensional `K`-invariant subspace
    left
    refine ⟨subOfSubmodule M U, subOfSubmodule_le M U,
      (fun h => hUne ((subOfSubmodule_eq_bot_iff M U).mp h)), ?_, ?_⟩
    · rw [card_subOfSubmodule]
      haveI : Fintype ↥U := Fintype.ofFinite _
      have h1 := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := ↥U)
      rw [ZMod.card] at h1
      rw [Nat.card_eq_fintype_card, h1, hUfr, pow_one]
    · intro k hk u hu
      have hkL : k ∈ (Work.ThmF.Ksub H t ⊔ P) :=
        (le_sup_left : Work.ThmF.Ksub H t ≤ Work.ThmF.Ksub H t ⊔ P) hk
      have hmemK : (⟨k, hkL⟩ : ↥(Work.ThmF.Ksub H t ⊔ P)) ∈
          (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P) :=
        Subgroup.mem_subgroupOf.mpr hk
      exact (conjRepOfLe_mem_subOfSubmodule_iff (n := ℓ) hLN ⟨k, hkL⟩ U).mp
        (hUinv ⟨k, hkL⟩ hmemK) u hu
  · -- Case 2: `M` is irreducible as a `K`-module
    right
    intro N hNle hNne hNinv
    set W : Submodule (ZMod ℓ) (Additive ↥M) := submoduleOfSub (n := ℓ) M N with hW
    have hSW : subOfSubmodule M W = N := by
      rw [hW, subOfSubmodule_submoduleOfSub, inf_eq_left.mpr hNle]
    have hWne : W ≠ ⊥ := by
      intro hbot
      exact hNne (by rw [← hSW, hbot, subOfSubmodule_bot])
    have hWinv : ∀ k ∈ (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P),
        ∀ w ∈ W, Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ)
          (Work.ThmF.Ksub H t ⊔ P) M hLN k w ∈ W := by
      intro k hk w hw
      have hkg : (k : G) ∈ Work.ThmF.Ksub H t := Subgroup.mem_subgroupOf.mp hk
      refine (conjRepOfLe_mem_subOfSubmodule_iff (n := ℓ) hLN k W).mpr ?_ w hw
      rw [hSW]
      exact fun n hn => hNinv (k : G) hkg n hn
    have htop : W = ⊤ := hKsim W hWinv hWne
    have hMN : subOfSubmodule M W = M := (subOfSubmodule_eq_M_iff M W).mpr htop
    rw [hSW] at hMN
    exact hMN

end Work.S3
