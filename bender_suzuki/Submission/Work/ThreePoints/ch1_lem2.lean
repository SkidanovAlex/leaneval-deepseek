import Mathlib
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I Ch. I §2 Lemma 2 (p. 152)

`H` is a strongly embedded subgroup of the finite group `G`, `H₁ = H^{g₁} ≠ H₂ = H^{g₂}` two
distinct conjugates of `H`, and `F ≤ G` is a subgroup whose intersections with both of them have
even order.  The conclusion is

* some involution `t ∈ F` conjugates `H₁` to `H₂`;
* `F ⊓ H₁` and `F ⊓ H₂` are strongly embedded (proper Bender) subgroups of `F`.

The two halves are independent of each other.

* **The involution.**  Since `|F ⊓ H₁|` and `|F ⊓ H₂|` are even, Cauchy supplies involutions
  `t ∈ F ⊓ H₁` and `s ∈ F ⊓ H₂`.  Because `G` acts on `Ω = G ⧸ H` and an involution of `G` fixes
  a *unique* point of `Ω`, `t` fixes the point `g₁H` uniquely and `s` the point `g₂H` uniquely;
  these points differ because their stabilisers `H₁ ≠ H₂` differ.  Hence `t` and `s` have no common
  fixed point, so `orderOf (t * s)` is odd and `t`, `s` are conjugate by an involution
  `u ∈ ⟨t, s⟩ ≤ F` (`Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul`).  Then
  `s * u = u * t`, so `u • (g₁H)` is fixed by `s`, hence equals `g₂H`; taking stabilisers gives
  `conj u H₁ = H₂`.

* **Strong embeddedness.**  This is Peterfalvi I Ch. I §1 (6) (`IsStronglyEmbedded.subgroupOf_inf`,
  from `Submission.Work.ThreePoints.Omega`), applied to the strongly embedded subgroup `Hᵢ` of `G`
  and the subgroup `F`: the order of `F ⊓ Hᵢ` is even by hypothesis, and `F ⊓ Hᵢ` is proper in `F`
  because otherwise `F ≤ Hᵢ`, whence `F ⊓ Hⱼ ≤ Hᵢ ⊓ Hⱼ` would have odd order
  (`card_inf_conj_odd`), contradicting the evenness of `F ⊓ Hⱼ`.

Both halves of the argument use only the geometry of `Ω` developed in
`Submission.Work.ThreePoints.Omega` / `Sec2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Two distinct conjugates of `H` intersected with `F` -/

/-- If `F ⊓ H₂` has even order then `F` is not contained in `H₁`, for two distinct conjugates
`H₁ ≠ H₂` of a strongly embedded subgroup: `F ≤ H₁` would force `F ⊓ H₂ ≤ H₁ ⊓ H₂`, a group of
odd order (`card_inf_conj_odd`). -/
theorem not_le_conj_of_even_card_inf {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {F : Subgroup G} {g₁ g₂ : G} (hne : conj g₁ H ≠ conj g₂ H)
    (h₂ : Even (Nat.card (F ⊓ conj g₂ H : Subgroup G))) : ¬ F ≤ conj g₁ H := by
  intro hle
  have hsub : F ⊓ conj g₂ H ≤ conj g₁ H ⊓ conj g₂ H :=
    le_inf (le_trans inf_le_left hle) inf_le_right
  have hodd : Odd (Nat.card (F ⊓ conj g₂ H : Subgroup G)) :=
    Odd.of_dvd (Subgroup.card_dvd_of_le hsub) (card_inf_conj_odd hH hne)
  exact (Nat.not_even_iff_odd.mpr hodd) h₂

/-- **Peterfalvi I Ch. I §1 (6)** in the form needed here: for two distinct conjugates `Hᵢ` of a
strongly embedded subgroup `H`, if `F ⊓ Hᵢ` has even order then it is a strongly embedded
subgroup of `F`. -/
theorem isStronglyEmbedded_inf_conj_subgroupOf {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {F : Subgroup G} {g₁ g₂ : G} (hne : conj g₁ H ≠ conj g₂ H)
    (h₁ : Even (Nat.card (F ⊓ conj g₁ H : Subgroup G)))
    (h₂ : Even (Nat.card (F ⊓ conj g₂ H : Subgroup G))) :
    IsStronglyEmbedded ((F ⊓ conj g₁ H).subgroupOf F : Subgroup ↥F) ∧
      IsStronglyEmbedded ((F ⊓ conj g₂ H).subgroupOf F : Subgroup ↥F) := by
  constructor
  · refine Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf
      (conj_stronglyEmbedded hH g₁) ?_ h₁
    intro htop
    exact not_le_conj_of_even_card_inf hH hne h₂
      (le_trans (Subgroup.subgroupOf_eq_top.mp htop) inf_le_right)
  · refine Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf
      (conj_stronglyEmbedded hH g₂) ?_ h₂
    intro htop
    exact not_le_conj_of_even_card_inf hH hne.symm h₁
      (le_trans (Subgroup.subgroupOf_eq_top.mp htop) inf_le_right)

/-! ## 2. The involution conjugating `H₁` to `H₂` -/

/-- **Peterfalvi I Ch. I §2 Lemma 2**, first assertion.  Some involution of `F` conjugates `H₁` to
`H₂`. -/
theorem exists_involution_conj_of_even_card_inf {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {F : Subgroup G} {g₁ g₂ : G} (hne : conj g₁ H ≠ conj g₂ H)
    (h₁ : Even (Nat.card (F ⊓ conj g₁ H : Subgroup G)))
    (h₂ : Even (Nat.card (F ⊓ conj g₂ H : Subgroup G))) :
    ∃ t ∈ involutions (F : Set G), conj t (conj g₁ H) = conj g₂ H := by
  classical
  -- (1) an involution in each intersection, by Cauchy's theorem
  have key : ∀ K : Subgroup G, Even (Nat.card (F ⊓ K : Subgroup G)) →
      ∃ t : G, t ∈ F ∧ t ∈ K ∧ orderOf t = 2 := by
    intro K hK
    haveI : Fintype ↥(F ⊓ K : Subgroup G) := Fintype.ofFinite ↥(F ⊓ K : Subgroup G)
    have hdvd : 2 ∣ Fintype.card ↥(F ⊓ K : Subgroup G) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp hK
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hdvd
    refine ⟨(x : G), x.2.1, x.2.2, ?_⟩
    rw [← Subgroup.orderOf_mk (x : G) x.2]
    exact hx
  obtain ⟨t₀, ht₀F, ht₀K, ht₀⟩ := key (conj g₁ H) h₁
  obtain ⟨s₀, hs₀F, hs₀K, hs₀⟩ := key (conj g₂ H) h₂
  -- (2) the two points of `Ω` and their stabilisers
  set ω₁ : G ⧸ H := (g₁ : G ⧸ H) with hω₁
  set ω₂ : G ⧸ H := (g₂ : G ⧸ H) with hω₂
  have hfix₁ : t₀ • ω₁ = ω₁ := by
    have hmem : t₀ ∈ MulAction.stabilizer G ω₁ := by
      rw [hω₁, stabilizer_mk H g₁]
      exact ht₀K
    exact MulAction.mem_stabilizer_iff.mp hmem
  have hfix₂ : s₀ • ω₂ = ω₂ := by
    have hmem : s₀ ∈ MulAction.stabilizer G ω₂ := by
      rw [hω₂, stabilizer_mk H g₂]
      exact hs₀K
    exact MulAction.mem_stabilizer_iff.mp hmem
  -- (3) an involution has a unique fixed point
  obtain ⟨a₁, ha₁⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers hH ht₀)
  obtain ⟨a₂, ha₂⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers hH hs₀)
  have hmem₁ : ω₁ ∈ fixedPts H (Subgroup.zpowers t₀) := by
    rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact hfix₁
  have hmem₂ : ω₂ ∈ fixedPts H (Subgroup.zpowers s₀) := by
    rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact hfix₂
  have hω₁a : ω₁ = a₁ := by
    rw [ha₁] at hmem₁
    exact Set.mem_singleton_iff.mp hmem₁
  have hω₂a : ω₂ = a₂ := by
    rw [ha₂] at hmem₂
    exact Set.mem_singleton_iff.mp hmem₂
  have fix₁ : ∀ ω : G ⧸ H, t₀ • ω = ω → ω = ω₁ := by
    intro ω hω
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t₀) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hω
    rw [ha₁] at hmem
    exact (Set.mem_singleton_iff.mp hmem).trans hω₁a.symm
  have fix₂ : ∀ ω : G ⧸ H, s₀ • ω = ω → ω = ω₂ := by
    intro ω hω
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers s₀) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hω
    rw [ha₂] at hmem
    exact (Set.mem_singleton_iff.mp hmem).trans hω₂a.symm
  -- (4) the two points are distinct, since their stabilisers are
  have hpt : ω₁ ≠ ω₂ := by
    intro h
    refine hne ?_
    have hs : MulAction.stabilizer G ω₁ = MulAction.stabilizer G ω₂ := by rw [h]
    rw [hω₁, hω₂, stabilizer_mk H g₁, stabilizer_mk H g₂] at hs
    exact hs
  -- (5) `t₀` and `s₀` have no common fixed point, so they are conjugate in a dihedral group
  have hsep : ∀ ω : G ⧸ H, t₀ • ω = ω → s₀ • ω ≠ ω := by
    intro ω hω hsω
    exact hpt ((fix₁ ω hω).symm.trans (fix₂ ω hsω))
  obtain ⟨u, hu2, hconj, hu_mem⟩ :=
    exists_involution_conj_of_odd_orderOf_mul ht₀ hs₀ (odd_orderOf_mul hH ht₀ hs₀ hsep)
  have huF : u ∈ F := by
    have hsub : Subgroup.closure ({t₀, s₀} : Set G) ≤ F :=
      (Subgroup.closure_le F).mpr (by rintro x (rfl | rfl) <;> assumption)
    exact hsub hu_mem
  -- (6) `u` carries the fixed point of `t₀` to that of `s₀`
  have hs₀u : s₀ * u = u * t₀ := by
    rw [← hconj]
    group
  have hfixu : s₀ • (u • ω₁) = u • ω₁ := by
    rw [← mul_smul, hs₀u, mul_smul, hfix₁]
  have huω : u • ω₁ = ω₂ := fix₂ (u • ω₁) hfixu
  have huω' : ((u * g₁ : G) : G ⧸ H) = ((g₂ : G) : G ⧸ H) := by
    rw [← smul_mk H u g₁, ← hω₁, ← hω₂]
    exact huω
  refine ⟨u, ⟨huF, hu2⟩, ?_⟩
  rw [← conj_mul u g₁ H, ← stabilizer_mk H (u * g₁), ← stabilizer_mk H g₂]
  exact congrArg (fun ω : G ⧸ H => MulAction.stabilizer G ω) huω'

/-! ## 3. Peterfalvi I Ch. I §2 Lemma 2 -/

/-- **Peterfalvi I Ch. I §2 Lemma 2** (p.152).  Let `H` be a strongly embedded subgroup, `H₁ ≠ H₂`
two conjugates of `H` and `F ≤ G` a subgroup whose intersections with both have even order.
Then there is an involution `t ∈ F` with `H₂ = t H₁ t⁻¹`, and `F ⊓ H₁`, `F ⊓ H₂` are strongly
embedded (proper Bender) subgroups of `F`. -/
theorem ch1_lem2 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {F : Subgroup G} {g₁ g₂ : G}
    (hne : Submission.Blueprint.conj g₁ H ≠ Submission.Blueprint.conj g₂ H)
    (h1 : Even (Nat.card (F ⊓ Submission.Blueprint.conj g₁ H : Subgroup G)))
    (h2 : Even (Nat.card (F ⊓ Submission.Blueprint.conj g₂ H : Subgroup G))) :
    (∃ t ∈ Submission.Blueprint.involutions (F : Set G),
        Submission.Blueprint.conj t (Submission.Blueprint.conj g₁ H) =
          Submission.Blueprint.conj g₂ H) ∧
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded
        ((F ⊓ Submission.Blueprint.conj g₁ H).subgroupOf F : Subgroup ↥F) ∧
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded
        ((F ⊓ Submission.Blueprint.conj g₂ H).subgroupOf F : Subgroup ↥F) :=
  ⟨exists_involution_conj_of_even_card_inf hH hne h1 h2,
    isStronglyEmbedded_inf_conj_subgroupOf hH hne h1 h2⟩

end Work.ThreePoints
