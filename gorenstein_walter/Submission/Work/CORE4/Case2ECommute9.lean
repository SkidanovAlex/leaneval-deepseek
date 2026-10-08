import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.L2TorusNormE

namespace Work.CORE4

variable {G : Type} [Group G] [Finite G]

open Subgroup

set_option linter.style.haveILetI false

/-! ## Elementary transport lemmas

Two subgroups of a cyclic finite group having the same cardinality coincide; this is
`Subgroup.IsCyclic.subgroup_eq_iff_card_eq` transported along `H ↦ H.subgroupOf C`. -/

/-- If `X ≤ Y` then `X.subgroupOf Y` has the same cardinality as `X`. -/
private lemma card_subgroupOf_of_le {G : Type*} [Group G] {X Y : Subgroup G} (h : X ≤ Y) :
    Nat.card ↥(X.subgroupOf Y) = Nat.card ↥X := by
  have h1 := Subgroup.card_map_of_injective (f := Y.subtype) (K := X.subgroupOf Y)
    Y.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h] at h1
  exact h1.symm

/-- In a finite cyclic group, two subgroups of the same cardinality coincide. -/
private lemma eq_of_le_of_card_eq_of_isCyclic {G : Type*} [Group G] [Finite G]
    {C : Subgroup G} (hC : IsCyclic ↥C) {A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hcard : Nat.card ↥A = Nat.card ↥B) : A = B := by
  haveI : IsCyclic ↥C := hC
  have hcard' : Nat.card ↥(A.subgroupOf C) = Nat.card ↥(B.subgroupOf C) := by
    rw [card_subgroupOf_of_le hA, card_subgroupOf_of_le hB, hcard]
  have hsub : A.subgroupOf C = B.subgroupOf C :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard'
  calc A = Subgroup.map C.subtype (A.subgroupOf C) :=
        (Subgroup.map_subgroupOf_eq_of_le hA).symm
    _ = Subgroup.map C.subtype (B.subgroupOf C) := by rw [hsub]
    _ = B := Subgroup.map_subgroupOf_eq_of_le hB

/-- In the §4 configuration, two subgroups of `E(M) = layerIn h.D.M` of order `p` (`p` any prime dividing `|F|`) that commute are equal: the centraliser in `E(M) ≅ L₂(q)` of an order-`p` subgroup is cyclic (`I.l2torusNorm`, using `p ∤ q`, which follows from `p ∣ |K₀|`, `K₀ ≤ K`, `k = |K||S₀|` and `gcd(k,q) = 1`), and a cyclic group has a unique subgroup of order `p`. -/
theorem Case2ECommute9 (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B) (h : Work.GW2.Case2Ctx B)
    (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (Y₀ Y₁ : Subgroup G) (h₀ : Y₀ ≤ Work.GW2.layerIn h.D.M) (h₁ : Y₁ ≤ Work.GW2.layerIn h.D.M)
    (hc₀ : Nat.card Y₀ = p) (hc₁ : Nat.card Y₁ = p)
    (hcomm : Y₀ ≤ Subgroup.centralizer (Y₁ : Set G)) : Y₀ = Y₁ := by
  -- `p` divides `|K₀|`, hence `|K|`, hence `p` is odd.
  obtain ⟨A, _hobj, hfacts⟩ := h8 p P hpp hPF hPcard
  have hp_dvd_K0 : p ∣ Nat.card ↥h.D.K0 := hfacts.1
  have hK0_le_K : h.D.K0 ≤ h.D.K := inf_le_right
  have hp_dvd_K : p ∣ Nat.card ↥h.D.K :=
    hp_dvd_K0.trans (Subgroup.card_dvd_of_le hK0_le_K)
  have hK_odd : Odd (Nat.card ↥h.D.K) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le (h.D.K_le_U B))
  have hp_odd : Odd p := Odd.of_dvd_nat hK_odd hp_dvd_K
  have hp_ne_two : p ≠ 2 := by
    obtain ⟨j, hj⟩ := hp_odd
    rintro rfl
    omega
  -- `k = |K| |S₀|` with `2k = q ∓ 1`, so `p ∤ q` and `p ≠ nineP h`.
  obtain ⟨k, k', hqodd, hq7, _hkeven, _hk'odd, hdisj, hrel⟩ := Case2ParityQOf G I hbc B h
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Case2KmulS0 G I hbc B h (Work.CORE4.qOf h) k k' hqodd hq7 hdisj hrel
  have hp_dvd_k : p ∣ k := by
    rw [hkK]; exact dvd_mul_of_dvd_left hp_dvd_K _
  have hp_not_dvd_q : ¬ p ∣ Work.CORE4.qOf h := by
    intro hpq
    have h2k : p ∣ 2 * k := dvd_mul_of_dvd_right hp_dvd_k 2
    rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1] at h2k
      have hd : p ∣ Work.CORE4.qOf h + 1 - Work.CORE4.qOf h := Nat.dvd_sub h2k hpq
      rw [Nat.add_sub_cancel_left] at hd
      exact hpp.not_dvd_one hd
    · rw [h1] at h2k
      have hd : p ∣ Work.CORE4.qOf h - (Work.CORE4.qOf h - 1) := Nat.dvd_sub hpq h2k
      have hone : Work.CORE4.qOf h - (Work.CORE4.qOf h - 1) = 1 := by omega
      rw [hone] at hd
      exact hpp.not_dvd_one hd
  have hp_ne_pF : p ≠ Work.CORE4.nineP h := by
    intro heq
    apply hp_not_dvd_q
    have hk0 : Work.CORE4.nineK h ≠ 0 := by
      intro h0
      have : Work.CORE4.qOf h = 1 := by rw [Work.CORE4.qOf, h0, pow_zero]
      omega
    rw [Work.CORE4.qOf, ← heq]
    exact dvd_pow_self p hk0
  -- `Y₁` is abelian, so it is contained in its own centraliser.
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : IsCyclic ↥Y₁ := isCyclic_of_prime_card hc₁
  haveI : CommGroup ↥Y₁ := IsCyclic.commGroup
  have hY1_cz : Y₁ ≤ Subgroup.centralizer (Y₁ : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hY0_le_C : Y₀ ≤ Subgroup.centralizer (Y₁ : Set G) ⊓ Work.GW2.layerIn h.D.M :=
    le_inf hcomm h₀
  have hY1_le_C : Y₁ ≤ Subgroup.centralizer (Y₁ : Set G) ⊓ Work.GW2.layerIn h.D.M :=
    le_inf hY1_cz h₁
  -- The centraliser of an order-`p` subgroup of `E(M) ≅ L₂(q)` is cyclic.
  have hcyc : IsCyclic ↥(Subgroup.centralizer (Y₁ : Set G) ⊓ Work.GW2.layerIn h.D.M) :=
    (L2TorusNormE I G hbc B h p Y₁ hpp hp_ne_two hp_ne_pF h₁ hc₁).1
  exact eq_of_le_of_card_eq_of_isCyclic hcyc hY0_le_C hY1_le_C (hc₀.trans hc₁.symm)

end Work.CORE4
