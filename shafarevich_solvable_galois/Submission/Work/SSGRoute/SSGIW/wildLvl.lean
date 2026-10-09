import Mathlib
import Submission.Work.SSGRoute.SSGIW.Basic
import Submission.Work.SSGRoute.SSGIW.coprime_card_sup
import Submission.Work.SSGRoute.PTWild.WildLevelStructure
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped Pointwise NumberField

namespace Work.SSGRoute

/-! ## The join of the normal subgroups of order coprime to `p` -/

section Generic

variable {H : Type*} [Group H] (p : ℕ)

instance instNonemptyWildFam : Nonempty (WildFam H p) :=
  ⟨⟨⊥, Subgroup.normal_bot, by rw [Subgroup.card_bot]; exact Nat.coprime_one_right p⟩⟩

theorem wildFam_directed : Directed (· ≤ ·) (fun Q : WildFam H p => Q.1) := by
  intro Q₁ Q₂
  haveI h1n : Q₁.1.Normal := Q₁.2.1
  haveI h2n : Q₂.1.Normal := Q₂.2.1
  refine ⟨⟨Q₁.1 ⊔ Q₂.1, Subgroup.sup_normal Q₁.1 Q₂.1,
    coprime_card_sup p Q₁.1 Q₂.1 Q₁.2.2 Q₂.2.2⟩, le_sup_left, le_sup_right⟩

theorem mem_iSup_wildFam {x : H} :
    x ∈ (⨆ Q : WildFam H p, Q.1) ↔ ∃ Q : WildFam H p, x ∈ Q.1 :=
  Subgroup.mem_iSup_of_directed (wildFam_directed p)

theorem normal_iSup_wildFam : (⨆ Q : WildFam H p, Q.1).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmap : (⨆ Q : WildFam H p, Q.1).map (MulAut.conj g).toMonoidHom
      = ⨆ Q : WildFam H p, Q.1 := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun Q => by
      haveI : Q.1.Normal := Q.2.1
      exact Subgroup.Normal.map_conj_eq Q.1 g
  have hmem : (MulAut.conj g) n ∈ (⨆ Q : WildFam H p, Q.1).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hn
  rw [hmap] at hmem
  rwa [MulAut.conj_apply] at hmem

theorem coprime_card_iSup_wildFam (hp : p.Prime) [Finite H] :
    Nat.Coprime p (Nat.card ↥(⨆ Q : WildFam H p, Q.1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨Q, hQ⟩ := (mem_iSup_wildFam p).mp (show ((x : H)) ∈ ⨆ Q : WildFam H p, Q.1 from x.2)
  let y : ↥Q.1 := ⟨(x : H), hQ⟩
  have hy : orderOf (x : H) = orderOf y := Subgroup.orderOf_coe y
  have hcop : Nat.Coprime p (orderOf y) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard y) Q.2.2
  rw [← hy, Subgroup.orderOf_coe, hx] at hcop
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] at hcop
  exact hp.ne_one hcop

theorem le_iSup_wildFam {Q : Subgroup H} (hQ : Q.Normal) (hc : Nat.Coprime p (Nat.card ↥Q)) :
    Q ≤ ⨆ Q : WildFam H p, Q.1 :=
  le_iSup (fun Q : WildFam H p => Q.1) ⟨Q, hQ, hc⟩

theorem isCyclic_quotient_of_zpowers_generator {W : Subgroup H} [W.Normal] (g : H)
    (h : ∀ δ : H, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ W) : IsCyclic (H ⧸ W) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨QuotientGroup.mk' W g, ?_⟩
  rw [Subgroup.eq_top_iff']
  intro y
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk'_surjective W y
  obtain ⟨m, hm⟩ := h δ
  have h1 : (QuotientGroup.mk' W δ)⁻¹ * (QuotientGroup.mk' W g) ^ m = 1 := by
    rw [← map_zpow, ← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hm
  rw [inv_mul_eq_one.mp h1]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩

end Generic

/-! ## The wild inertia of a level inertia -/

section Level

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)

theorem wildLvl_normal (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] : (wildLvl p k Ω A hA M).Normal :=
  normal_iSup_wildFam (H := ↥(levelInertiaOf k Ω A hA M)) p

theorem wildLvl_coprime (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] : Nat.Coprime p (Nat.card ↥(wildLvl p k Ω A hA M)) := by
  haveI : Fintype (↥M ≃ₐ[k] ↥M) := AlgEquiv.fintype k ↥M
  haveI : Finite ↥(levelInertiaOf k Ω A hA M) :=
    Finite.of_injective (fun x : ↥(levelInertiaOf k Ω A hA M) => (x : ↥M ≃ₐ[k] ↥M))
      Subtype.val_injective
  exact coprime_card_iSup_wildFam (H := ↥(levelInertiaOf k Ω A hA M)) p (Fact.out)

theorem wildLvl_le_of_normal (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M]
    [NumberField ↥M] {Q : Subgroup ↥(levelInertiaOf k Ω A hA M)} (hQ : Q.Normal)
    (hc : Nat.Coprime p (Nat.card ↥Q)) : Q ≤ wildLvl p k Ω A hA M :=
  le_iSup_wildFam p hQ hc

/-- **`I_M` modulo the wild inertia is cyclic**, in generator form. -/
theorem wildLvl_generator (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) (M : IntermediateField k Ω)
    [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ∃ g : ↥(levelInertiaOf k Ω A hA M), ∀ δ : ↥(levelInertiaOf k Ω A hA M),
      ∃ m : ℤ, δ⁻¹ * g ^ m ∈ wildLvl p k Ω A hA M := by
  obtain ⟨W, ℓ, a, hWle, hWnorm, hℓp, hℓne, hWcard, g, hg, hgen⟩ :=
    Work.SSGRoute.PTWild.levelInertiaNormalProEll_axf p k Ω A hA h M
  let Q : Subgroup ↥(levelInertiaOf k Ω A hA M) := W.subgroupOf _
  haveI hQn : Q.Normal :=
    ⟨fun n hn x => hWnorm x x.2 n (Subgroup.mem_subgroupOf.mp hn)⟩
  have hQcard : Nat.card ↥Q = ℓ ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv, hWcard]
  have hcop : Nat.Coprime p (Nat.card ↥Q) := by
    rw [hQcard]
    exact ((Nat.coprime_primes (Fact.out : p.Prime) hℓp).mpr hℓne.symm).pow_right a
  have hQle : Q ≤ wildLvl p k Ω A hA M := wildLvl_le_of_normal p k Ω A hA M hQn hcop
  refine ⟨⟨g, hg⟩, fun δ => ?_⟩
  obtain ⟨m, hm⟩ := hgen (δ : ↥M ≃ₐ[k] ↥M) δ.2
  refine ⟨m, hQle ?_⟩
  rw [Subgroup.mem_subgroupOf]
  simpa using hm

end Level

end Work.SSGRoute
