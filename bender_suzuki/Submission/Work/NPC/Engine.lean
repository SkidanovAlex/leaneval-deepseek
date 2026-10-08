/-
Area A9 (normal `p`-complement theorems): the transfer engine.

The main tool of this area is `hasNormalPComplement_of_hom_to_pGroup`: if `φ : G →* A` is a
homomorphism to a `p`-group `A` whose restriction to a Sylow `p`-subgroup `P ≤ G` is injective,
then `ker φ` is a normal `p`-complement of `G`.  Every normal-`p`-complement theorem in the
literature (Burnside, Frobenius, Thompson, Glauberman–Thompson) is proved by exhibiting such a
`φ` — typically the transfer `G →* P/P*`, `G →* P'` or `G →* Z(N_G(J(P)))`.
-/
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open scoped Pointwise commutatorElement

namespace Work.NPC

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **The transfer engine.**  If `A` is a `p`-group and `φ : G →* A` is injective on a Sylow
`p`-subgroup `P`, then `ker φ` is a normal `p`-complement of `G`.

Indeed `|ker φ| · |G ⧸ ker φ| = |G|`, the image of `G` is a `p`-group containing an injective copy
of `P`, so it has order exactly the `p`-part `|P|` of `|G|`; hence `|ker φ| = [G : P]` is coprime
to `p`. -/
theorem hasNormalPComplement_of_hom_to_pGroup {A : Type*} [Group A] [Finite A]
    (P : Sylow p G) (φ : G →* A) (hA : IsPGroup p A)
    (hφ : Function.Injective (φ.domRestrict (P : Subgroup G))) :
    HasNormalPComplement p G := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  obtain ⟨n, hn⟩ := (IsPGroup.of_injective hA φ.range.subtype Subtype.coe_injective).exists_card_eq
  -- `φ` is injective on `P`
  have hφ' : ∀ x y : ↥(P : Subgroup G), φ (x : G) = φ (y : G) → x = y :=
    fun x y hxy => hφ (by simpa using hxy)
  -- cardinality of the kernel times the cardinality of the range
  have hker_card : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card G := by
    rw [← Subgroup.card_mul_index φ.ker]
    congr 1
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  have hPmul : Nat.card ↥(P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
    Subgroup.card_mul_index _
  have hPle : Nat.card ↥(P : Subgroup G) ≤ Nat.card ↥φ.range := by
    refine Nat.card_le_card_of_injective (fun x : ↥(P : Subgroup G) => (⟨φ x, ⟨x, rfl⟩⟩ : ↥φ.range)) ?_
    intro x y hxy
    exact hφ' x y (congrArg Subtype.val hxy)
  have hPnd : ¬ p ∣ (P : Subgroup G).index := P.not_dvd_index
  -- `p ^ n ∣ p ^ m` and `p ^ m ≤ p ^ n`
  have hmain : Nat.card ↥φ.ker * p ^ n = p ^ m * (P : Subgroup G).index := by
    rw [← hn, ← hm, hker_card, hPmul]
  have hpn_dvd : p ^ n ∣ p ^ m := by
    have hc : (p ^ n).Coprime (P : Subgroup G).index :=
      (hp.coprime_pow_of_not_dvd hPnd).symm
    exact hc.dvd_of_dvd_mul_right (hmain ▸ dvd_mul_left (p ^ n) (Nat.card ↥φ.ker))
  have hnm : n ≤ m := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpn_dvd
  have hmn : m ≤ n := by
    rw [hm, hn] at hPle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hPle
  have hker_eq : Nat.card ↥φ.ker = (P : Subgroup G).index := by
    refine Nat.mul_right_cancel (pow_pos hp.pos n) ?_
    rw [hmain, le_antisymm hmn hnm, mul_comm]
  refine ⟨φ.ker, MonoidHom.normal_ker φ, ?_, ?_⟩
  · rw [hker_eq]
    exact (hp.coprime_iff_not_dvd.mpr hPnd).symm
  · exact IsPGroup.of_equiv (IsPGroup.of_injective hA φ.range.subtype Subtype.coe_injective)
      (QuotientGroup.quotientKerEquivRange φ).symm

/-- **Burnside's normal `p`-complement theorem.**  If the Sylow `p`-subgroup `P` is central in its
normalizer (`N_G(P) ≤ C_G(P)`), then `G` has a normal `p`-complement.  (Mathlib has this as
`MonoidHom.ker_transferSylow_isComplement'`; here it is derived from the transfer engine by noting
that `transferSylow` restricts to the injective power map `x ↦ x ^ [G : P]` on `P`.) -/
theorem burnside_npc (P : Sylow p G)
    (h : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G)) :
    HasNormalPComplement p G := by
  have hpow : ⇑(P.isPGroup'.powEquiv' P.not_dvd_index) =
      fun x : ↥(P : Subgroup G) => x ^ (P : Subgroup G).index := by
    funext x
    simp
  have hinj : Function.Injective (fun x : ↥(P : Subgroup G) => x ^ (P : Subgroup G).index) := by
    rw [← hpow]
    exact (P.isPGroup'.powEquiv' P.not_dvd_index).injective
  refine hasNormalPComplement_of_hom_to_pGroup P (MonoidHom.transferSylow P h) P.isPGroup' ?_
  rw [MonoidHom.transferSylow_domRestrict_eq_pow]
  exact hinj

/-- If the focal subgroup of a Sylow `p`-subgroup `P` is trivial, then `G` has a normal
`p`-complement.  (The transfer `V : G →* P ⧸ P*` is injective on `P` and its image is a
`p`-group.) -/
theorem hasNormalPComplement_of_focalSubgroup_eq_bot (P : Sylow p G)
    (h : (P : Subgroup G).focalSubgroup = ⊥) : HasNormalPComplement p G := by
  have hfoc : (P : Subgroup G).focalSubgroupOf = ⊥ := by
    rw [Subgroup.focalSubgroupOf_def, h, Subgroup.bot_subgroupOf]
  have hpowinj : Function.Injective (fun x : ↥(P : Subgroup G) => x ^ (P : Subgroup G).index) := by
    have hpow : ⇑(P.isPGroup'.powEquiv' P.not_dvd_index) =
        fun x : ↥(P : Subgroup G) => x ^ (P : Subgroup G).index := by
      funext x
      simp
    rw [← hpow]
    exact (P.isPGroup'.powEquiv' P.not_dvd_index).injective
  refine hasNormalPComplement_of_hom_to_pGroup P (P : Subgroup G).transferFocal ?_ ?_
  · exact IsPGroup.to_quotient P.isPGroup' _
  · rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [Subgroup.mem_bot, MonoidHom.mem_ker, MonoidHom.domRestrict_apply,
      Subgroup.transferFocal_eq_pow]
    constructor
    · intro hx
      have hxmem : x ^ (P : Subgroup G).index ∈ (P : Subgroup G).focalSubgroupOf := by
        rw [← QuotientGroup.ker_mk' (P : Subgroup G).focalSubgroupOf]
        exact MonoidHom.mem_ker.mpr (by rw [map_pow]; exact hx)
      have hx1 : x ^ (P : Subgroup G).index = 1 := by
        have := hxmem
        rw [hfoc] at this
        simpa using this
      exact hpowinj (by simpa using hx1)
    · intro hx
      rw [hx]
      simp

/-- If no two distinct elements of a Sylow `p`-subgroup `P` are conjugate in `G`, then `G` has a
normal `p`-complement.  (Then the focal subgroup of `P` is trivial.) -/
theorem hasNormalPComplement_of_trivial_fusion_sylow (P : Sylow p G)
    (h : ∀ x y : ↥(P : Subgroup G), IsConj (x : G) (y : G) → x = y) :
    HasNormalPComplement p G := by
  refine hasNormalPComplement_of_focalSubgroup_eq_bot P ?_
  refine le_antisymm ?_ bot_le
  rw [Subgroup.focalSubgroup_def]
  refine (Subgroup.closure_le (⊥ : Subgroup G)).mpr ?_
  rintro g ⟨hgP, x, hxP, u, rfl⟩
  change ⁅x, u⁆ ∈ (⊥ : Subgroup G)
  rw [Subgroup.mem_bot]
  have hconj_mem : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h1 : u * x * u⁻¹ = ⁅x, u⁆⁻¹ * x := by rw [commutatorElement_def]; group
    rw [h1]
    exact P.mul_mem (P.inv_mem hgP) hxP
  have hconj : IsConj (x : G) (u * x * u⁻¹ : G) :=
    isConj_iff.mpr ⟨(⟨u, u⁻¹, mul_inv_cancel u, inv_mul_cancel u⟩ : Gˣ), by simp⟩
  have heq : (⟨x, hxP⟩ : ↥(P : Subgroup G)) = ⟨u * x * u⁻¹, hconj_mem⟩ :=
    h ⟨x, hxP⟩ ⟨u * x * u⁻¹, hconj_mem⟩ hconj
  have heq2 : x = u * x * u⁻¹ := by simpa using congrArg Subtype.val heq
  have h1 : ⁅x, u⁆ = x * (u * x * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [h1, ← heq2, mul_inv_cancel]

end Work.NPC
