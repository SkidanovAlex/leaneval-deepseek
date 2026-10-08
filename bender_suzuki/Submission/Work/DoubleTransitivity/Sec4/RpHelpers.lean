import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.App2.sylow_max_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec4.RpHelpers`

Elementary helpers for Ch. I §3–§4: the §3 remark (even normaliser + two fixed points ⟹ three
fixed points), conjugation invariance of the number of fixed points, the existence of a maximal
`p`-subgroup with three fixed points containing a given one, and the existence of a `p`-Sylow of
a subgroup containing a given `p`-subgroup.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.DoubleTransitivity.Sec4

variable {G : Type} [Group G]

/-- The stabiliser of the canonical point `pt H` of `Ω = G ⧸ H` is `H`. -/
theorem stabilizer_pt_eq (H : Subgroup G) : MulAction.stabilizer G (pt H) = H := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_pt, mk_one_eq_iff]

/-- `ω ∈ fixedPts H X` iff `X` is contained in the stabiliser of `ω`. -/
theorem mem_fixedPts_iff_le_stabilizer_aux {H X : Subgroup G} {ω : Omega H} :
    ω ∈ fixedPts H X ↔ X ≤ MulAction.stabilizer G ω := by
  rw [fixedPts, Set.mem_ofPred_eq, SetLike.le_def]
  constructor
  · intro h x hx
    rw [MulAction.mem_stabilizer_iff]
    exact h x hx
  · intro h x hx
    exact MulAction.mem_stabilizer_iff.mp (h hx)

/-- The number of fixed points of a subgroup is invariant under conjugation. -/
theorem ncard_fixedPts_conj (H : Subgroup G) (g : G) (Q : Subgroup G) :
    (fixedPts H (conj g Q)).ncard = (fixedPts H Q).ncard := by
  have hset : fixedPts H (conj g Q) = g • fixedPts H Q := by
    ext ω
    rw [Set.mem_smul_set]
    constructor
    · intro hω
      refine ⟨g⁻¹ • ω, ?_, by rw [smul_inv_smul]⟩
      intro q hq
      have hmem : g * q * g⁻¹ ∈ conj g Q :=
        ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have h1 : (g * q * g⁻¹) • ω = ω := hω _ hmem
      calc q • (g⁻¹ • ω) = (q * g⁻¹) • ω := by rw [mul_smul]
        _ = (g⁻¹ * (g * q * g⁻¹)) • ω := by
              rw [show q * g⁻¹ = g⁻¹ * (g * q * g⁻¹) from by group]
        _ = g⁻¹ • ((g * q * g⁻¹) • ω) := by rw [mul_smul]
        _ = g⁻¹ • ω := by rw [h1]
    · rintro ⟨y, hy, rfl⟩
      rintro x ⟨q, hq, rfl⟩
      have hqy : q • y = y := hy q hq
      calc (g * q * g⁻¹) • (g • y) = ((g * q * g⁻¹) * g) • y := by rw [← mul_smul]
        _ = (g * q) • y := by rw [show (g * q * g⁻¹) * g = g * q from by group]
        _ = g • (q • y) := by rw [mul_smul]
        _ = g • y := by rw [hqy]
  rw [hset, Set.ncard_smul_set]

variable [Finite G]

/-- **Ch. I §3 (p. 154)**: if a `p`-subgroup `P` fixes at least two points and some point
stabiliser `N_G(P) ⊓ Stab ω₁` has even order, then `P` fixes at least three points. -/
theorem three_le_fixedPts_of_even_normalizer {H : Subgroup G} (hH : IsBender H) {P : Subgroup G}
    {ω₁ : Omega H} (hω₁ : ω₁ ∈ fixedPts H P)
    (hEven : Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω₁)))
    (h2 : 2 ≤ (fixedPts H P).ncard) : 3 ≤ (fixedPts H P).ncard := by
  rcases lt_or_ge 2 (fixedPts H P).ncard with h | h
  · omega
  · exfalso
    have hcard : (fixedPts H P).ncard = 2 := le_antisymm h h2
    obtain ⟨ω₂, hω₂, hω₂ne⟩ := Set.exists_ne_of_one_lt_ncard (s := fixedPts H P) (by omega) ω₁
    have hset : fixedPts H P = ({ω₁, ω₂} : Set (Omega H)) := by
      refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
      · intro ω hω
        rcases hω with rfl | rfl
        · exact hω₁
        · exact hω₂
      · rw [Set.ncard_pair hω₂ne.symm, hcard]
    -- an involution `t ∈ N_G(P) ⊓ Stab ω₁`
    haveI : Fintype ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω₁) :=
      Fintype.ofFinite _
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (G :=
      ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω₁)) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hEven)
    have ht2 : orderOf ((t : G)) = 2 := (Subgroup.orderOf_coe t).trans ht
    have htP : (t : G) ∈ Subgroup.normalizer (P : Set G) := t.2.1
    have htω₁ : (t : G) • ω₁ = ω₁ := MulAction.mem_stabilizer_iff.mp t.2.2
    -- `t` permutes `Ω_P = {ω₁, ω₂}`
    have hmem : (t : G) • ω₂ ∈ fixedPts H P :=
      Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer htP hω₂
    rw [hset, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hmem | hmem
    · have h3 : (t : G) • ((t : G) • ω₂) = (t : G) • ω₁ := by rw [hmem, htω₁]
      rw [← mul_smul, Work.DoubleTransitivity.App1.mul_self_eq_one_of_orderOf_eq_two ht2,
        one_smul] at h3
      rw [htω₁] at h3
      exact hω₂ne h3
    · exact hω₂ne (Work.DoubleTransitivity.Sec1.eq_of_smul_eq_of_orderOf_eq_two hH ht2 hmem htω₁)

/-- There is a `p`-subgroup with at least three fixed points which contains a given one and is
maximal among the `p`-subgroups of `G` with at least three fixed points. -/
theorem exists_maxFixesThree_le {p : ℕ} {H Q₀ : Subgroup G}
    (h : ∃ Q : Subgroup G, IsPGroup p Q ∧ FixesThree H Q ∧ Q₀ ≤ Q) :
    ∃ Q : Subgroup G, Q₀ ≤ Q ∧ MaxFixesThree p H Q := by
  classical
  set φ : ℕ → Prop := fun m => ∃ Q : Subgroup G, Q₀ ≤ Q ∧ IsPGroup p Q ∧
      FixesThree H Q ∧ Nat.card ↥Q = m with hφ
  obtain ⟨Q, hQp, hQ3, hQ₀Q⟩ := h
  have hcard_le : ∀ R : Subgroup G, Nat.card ↥R ≤ Nat.card G := by
    intro R
    have hdvd : Nat.card ↥R ∣ Nat.card G := by
      have h1 := Subgroup.card_dvd_of_le (show R ≤ (⊤ : Subgroup G) from le_top)
      rwa [Subgroup.card_top] at h1
    exact Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨Q₁, hQ₀Q₁, hQ₁p, hQ₁3, hQ₁card⟩ :=
    Nat.findGreatest_spec (P := φ) (hcard_le Q) ⟨Q, hQ₀Q, hQp, hQ3, rfl⟩
  refine ⟨Q₁, hQ₀Q₁, hQ₁p, hQ₁3, ?_⟩
  intro Q₂ hQ₂p hQ₂3 hQ₁Q₂
  have hle : Nat.card ↥Q₂ ≤ Nat.card ↥Q₁ := by
    have hnotlt : ¬ Nat.card ↥Q₂ > Nat.findGreatest φ (Nat.card G) :=
      fun hlt => Nat.findGreatest_is_greatest hlt (hcard_le Q₂)
        ⟨Q₂, le_trans hQ₀Q₁ hQ₁Q₂, hQ₂p, hQ₂3, rfl⟩
    rw [hQ₁card]
    omega
  exact show Q₂ ≤ Q₁ from (Subgroup.eq_of_le_of_card_ge hQ₁Q₂ hle).ge

/-- A `p`-Sylow of `D` containing a given `p`-subgroup of `D`. -/
theorem exists_isSylowSubgroupOf_le {p : ℕ} [Fact p.Prime] {P D : Subgroup G} (hP : IsPGroup p P)
    (hPD : P ≤ D) : ∃ S : Subgroup G, P ≤ S ∧ IsSylowSubgroupOf p S D := by
  obtain ⟨S, hPS⟩ := (hP.comap_subtype (K := D)).exists_le_sylow
  refine ⟨(S : Subgroup ↥D).map D.subtype, ?_,
    Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype (Fact.out) S⟩
  calc P = (P.subgroupOf D).map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hPD).symm
    _ ≤ (S : Subgroup ↥D).map D.subtype := Subgroup.map_mono hPS

/-- A `p`-Sylow of a subgroup exists. -/
theorem exists_isSylowSubgroupOf_of_subgroup (p : ℕ) [Fact p.Prime] (D : Subgroup G) :
    ∃ S : Subgroup G, IsSylowSubgroupOf p S D := by
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥D)
  exact ⟨(S : Subgroup ↥D).map D.subtype,
    Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype (Fact.out) S⟩

/-- The `MulAut`-action on subgroups is conjugation by the challenge's `conj`. -/
theorem mulAut_conj_smul_eq_conj (g : G) (H : Subgroup G) :
    MulAut.conj g • H = conj g H := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

/-- **Sylow conjugacy**, in the form used below: a `p`-subgroup of `G` is contained in a conjugate
of any `p`-Sylow of `G`. -/
theorem exists_le_conj_of_isPGroup_isSylowSub {p : ℕ} [Fact p.Prime] {Q S : Subgroup G}
    (hQ : IsPGroup p Q) (hS : IsSylowSub p S) : ∃ g : G, Q ≤ conj g S := by
  obtain ⟨S', hQS'⟩ := hQ.exists_le_sylow
  obtain ⟨k, -, hk⟩ := Work.DoubleTransitivity.App2.sylow_max_conj (X := G) (p := p) (K := ⊤)
    S'.isPGroup' le_top (fun T hT hS'T _ => S'.is_maximal' hT hS'T)
    hS.1 le_top (fun T hT hST _ => (hS.1.toSylow hS.2).is_maximal' hT hST)
  exact ⟨k, by
    change Q ≤ Subgroup.map (MulAut.conj k).toMonoidHom S
    rw [hk]
    exact hQS'⟩

end Work.DoubleTransitivity.Sec4
