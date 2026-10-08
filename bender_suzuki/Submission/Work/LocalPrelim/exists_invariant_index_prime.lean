import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.Internal
import Submission.Work.LocalPrelim.exists_isInvariant_card_eq_prime
import Submission.Work.LocalPrelim.smul_eq_self_of_card_eq_prime
import Submission.Work.LocalPrelim.relIndex_sup_eq_relIndex_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

universe u

namespace Work.LocalPrelim

/-! ### Transport of invariance along equivariant maps -/

theorem smul_map_aux {G H : Type*} [Group G] [Group H] {α : Type*} [Group α]
    [MulDistribMulAction α G] [MulDistribMulAction α H] (f : G →* H)
    (hf : ∀ (a : α) (x : G), f (a • x) = a • f x) (K : Subgroup G) (a : α) :
    a • (K.map f) = (a • K).map f := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    rw [Subgroup.mem_map] at hy ⊢
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨a • x, ?_, ?_⟩
    · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; simpa using hx
    · rw [hf a x, hxy, smul_inv_smul]
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨k, hk, hkx⟩ := (Subgroup.mem_smul_pointwise_iff_exists x a K).mp hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
    exact ⟨k, hk, by rw [← hxy, ← hkx, hf a k, inv_smul_smul]⟩

theorem map_isInvariant_aux {G H : Type*} [Group G] [Group H] {α : Type*} [Group α]
    [MulDistribMulAction α G] [MulDistribMulAction α H] (f : G →* H)
    (hf : ∀ (a : α) (x : G), f (a • x) = a • f x) {K : Subgroup G} (hK : FT.IsInvariant α K) :
    FT.IsInvariant α (K.map f) :=
  ⟨fun a => by rw [smul_map_aux f hf K a, hK.smul_eq_self a]⟩

theorem comap_isInvariant_aux {G H : Type*} [Group G] [Group H] {α : Type*} [Group α]
    [MulDistribMulAction α G] [MulDistribMulAction α H] (f : G →* H)
    (hf : ∀ (a : α) (x : G), f (a • x) = a • f x) {K : Subgroup H} (hK : FT.IsInvariant α K) :
    FT.IsInvariant α (K.comap f) := by
  refine ⟨fun a => Subgroup.ext fun x => ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_comap, Subgroup.mem_comap,
    hf a⁻¹ x]
  exact hK.mem_smul_iff a⁻¹ (f x)

theorem subgroupOf_isInvariant_aux {α G : Type*} [Group α] [Group G] [MulDistribMulAction α G]
    {S Z : Subgroup G} [FT.IsInvariant α S] [FT.IsInvariant α Z] (hSZ : S ≤ Z) :
    FT.IsInvariant α (S.subgroupOf Z) := by
  refine ⟨fun a => Subgroup.ext fun x => ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    FT.coe_subgroup_smul]
  exact (inferInstance : FT.IsInvariant α S).mem_smul_iff a⁻¹ (x : G)

/-- `H.subgroupOf B` is invariant under the conjugation action of `Q` on `B` when `Q`
normalizes `H`. -/
theorem subgroupOf_isInvariant_conjAction {X : Type*} [Group X] {Q B H : Subgroup X}
    [FT.Normalizes Q B] (hQH : Q ≤ Subgroup.normalizer (H : Set X)) :
    FT.IsInvariant ↥Q (H.subgroupOf B) := by
  refine ⟨fun q => Subgroup.ext fun y => ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    FT.conj_smul_coe, Subgroup.coe_inv, inv_inv]
  exact (Subgroup.mem_normalizer_iff''.mp (hQH q.2) (y : X)).symm

/-! ### Two index computations -/

theorem ker_relIndex_comap {A B : Type*} [Group A] [Group B] (q : A →* B) (W : Subgroup B)
    (h : W ≤ q.range) : q.ker.relIndex (W.comap q) = Nat.card W := by
  rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq, inf_eq_right.mpr h]

/-! ### If `H` has index `p` in the `p`-group `B` and is normalized by the `p`-group `Q`, then
`[Q,B] ≤ H`. -/

theorem commutator_le_of_index_prime_normalizer {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {Q B H : Subgroup X} (hQp : IsPGroup p Q) (hBp : IsPGroup p B)
    (hQnB : Q ≤ Subgroup.normalizer (B : Set X)) (hQnH : Q ≤ Subgroup.normalizer (H : Set X))
    (hle : H ≤ B) (hidx : (H.subgroupOf B).index = p) : ⁅Q, B⁆ ≤ H := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `H ◁ B` because `[B : H] = p` is the smallest prime divisor of `|B|`.
  have hHnormal : (H.subgroupOf B).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hidx]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have h1 := Subgroup.index_mul_card (H.subgroupOf B)
      rw [hidx, hk] at h1
      have h2 : 1 < p * Nat.card ↥(H.subgroupOf B) := by
        have h3 : 0 < Nat.card ↥(H.subgroupOf B) := Nat.card_pos
        nlinarith [hp.two_le]
      linarith [h1, h2]
    rw [hk, Nat.Prime.pow_minFac hp hk0]
  haveI hNQ : FT.Normalizes Q B := ⟨hQnB⟩
  haveI : FT.IsInvariant ↥Q (H.subgroupOf B) := subgroupOf_isInvariant_conjAction hQnH
  -- The action on the `p`-element quotient is trivial, by counting fixed points.
  have htriv : FT.IsTrivialOn ↥Q (↥B ⧸ (H.subgroupOf B)) := by
    have hcard : Nat.card (↥B ⧸ (H.subgroupOf B)) = p := by
      rw [← Subgroup.index_eq_card]; exact hidx
    have hfix : (QuotientGroup.mk (1 : ↥B)) ∈
        MulAction.fixedPoints ↥Q (↥B ⧸ (H.subgroupOf B)) := by
      rw [MulAction.mem_fixedPoints]
      intro q
      rw [FT.quotient_smul_mk, smul_one]
    exact fun q x => smul_eq_self_of_card_eq_prime hp hQp hcard hfix q x
  have hcomm : FT.commutator ↥Q (⊤ : Subgroup ↥B) ≤ H.subgroupOf B :=
    (FT.isTrivialOn_quotient_iff (A := ↥Q) (G := ↥B) (N := H.subgroupOf B)).mp htriv
  calc ⁅Q, B⁆ = ⁅B, Q⁆ := Subgroup.commutator_comm Q B
    _ = (FT.commutator ↥Q (⊤ : Subgroup ↥B)).map B.subtype := (FT.commutator_conjAction Q B).symm
    _ ≤ (H.subgroupOf B).map B.subtype := Subgroup.map_mono hcomm
    _ = H ⊓ B := Subgroup.subgroupOf_map_subtype H B
    _ = H := inf_eq_left.mpr hle

/-! ### The abstract invariant-index-`p` lemma -/

theorem exists_invariant_index_prime_aux (p : ℕ) (hp : p.Prime)
    {Q : Type*} [Group Q] [Finite Q] (hQp : IsPGroup p Q) :
    ∀ (n : ℕ) {G : Type u} [Group G] [Finite G] [MulDistribMulAction Q G],
      Nat.card G = n → IsPGroup p G → (H : Subgroup G) → FT.IsInvariant Q H → H < ⊤ →
      ∃ B : Subgroup G, H ≤ B ∧ FT.IsInvariant Q B ∧ (H.subgroupOf B).index = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n
  refine Nat.strong_induction_on (p := fun n => ∀ {G : Type u} [Group G] [Finite G]
      [MulDistribMulAction Q G], Nat.card G = n → IsPGroup p G → (H : Subgroup G) →
      FT.IsInvariant Q H → H < ⊤ →
      ∃ B : Subgroup G, H ≤ B ∧ FT.IsInvariant Q B ∧ (H.subgroupOf B).index = p) n ?_
  intro m ih G _ _ _ hcard hG H hHinv hHlt
  have hGnt : Nontrivial G := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    refine hHlt.ne (le_antisymm le_top fun x _ => ?_)
    rw [Subsingleton.elim x 1]; exact H.one_mem
  haveI hGntI : Nontrivial G := hGnt
  haveI hHinvI : FT.IsInvariant Q H := hHinv
  by_cases hZle : Subgroup.center G ≤ H
  · -- Case A: the centre is contained in `H`; pass to the quotient by the centre.
    set f : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G) with hfdef
    have hfeq : ∀ (a : Q) (x : G), f (a • x) = a • f x := fun a x => rfl
    set H' : Subgroup (G ⧸ Subgroup.center G) := H.map f with hH'def
    have hH'inv : FT.IsInvariant Q H' := map_isInvariant_aux f hfeq hHinv
    have hHcomap : H'.comap f = H := by
      rw [hH'def, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZle]
    have hH'lt : H' < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      have : H = ⊤ := by rw [← hHcomap, htop, Subgroup.comap_top]
      exact hHlt.ne this
    have hGq : IsPGroup p (G ⧸ Subgroup.center G) := hG.to_quotient _
    have hcardq : Nat.card (G ⧸ Subgroup.center G) < m := by
      have h1 : Nat.card G = Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      haveI : Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hG
      have h2 : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
      have h3 : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
      rw [hcard] at h1
      nlinarith
    obtain ⟨B', hH'le, hB'inv, hidx'⟩ :=
      ih (Nat.card (G ⧸ Subgroup.center G)) hcardq rfl hGq H' hH'inv hH'lt
    refine ⟨B'.comap f, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_le_iff_le_comap]
      rwa [← hH'def]
    · exact comap_isInvariant_aux f hfeq hB'inv
    · show H.relIndex (B'.comap f) = p
      have hmapB : (B'.comap f).map f = B' :=
        Subgroup.map_comap_eq_self (by
          rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)
      have hkey : H.relIndex (B'.comap f) = H'.relIndex B' := by
        have h := Subgroup.relIndex_comap (H := H') (f := f) (K := B'.comap f)
        rw [hHcomap, hmapB] at h
        exact h
      rw [hkey]
      exact hidx'
  · -- Case B: the centre is not contained in `H`.
    have hZ1lt : H ⊓ Subgroup.center G < Subgroup.center G := by
      rw [lt_iff_le_and_ne]
      exact ⟨inf_le_right, fun heq => hZle (heq ▸ inf_le_left)⟩
    have hZ1subinv : FT.IsInvariant Q ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)) :=
      subgroupOf_isInvariant_aux inf_le_right
    haveI hZ1subinvI : FT.IsInvariant Q ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)) :=
      hZ1subinv
    have hnt : Nontrivial
        (↥(Subgroup.center G) ⧸ ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G))) := by
      rw [QuotientGroup.nontrivial_iff, Ne, Subgroup.subgroupOf_eq_top]
      exact fun h => hZle (le_trans h inf_le_left)
    have hZbarp : IsPGroup p
        (↥(Subgroup.center G) ⧸ ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G))) :=
      (hG.to_subgroup (Subgroup.center G)).to_quotient _
    obtain ⟨Wbar, hWbarinv, hWbarcard⟩ :=
      exists_isInvariant_card_eq_prime (Q := Q) hp hQp hZbarp hnt
    set q : ↥(Subgroup.center G) →*
        (↥(Subgroup.center G) ⧸ ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G))) :=
      QuotientGroup.mk' _ with hqdef
    have hqeq : ∀ (a : Q) (x : ↥(Subgroup.center G)), q (a • x) = a • q x := fun a x => rfl
    set W : Subgroup ↥(Subgroup.center G) := Wbar.comap q with hWdef
    have hWinv : FT.IsInvariant Q W := comap_isInvariant_aux q hqeq hWbarinv
    haveI hWinvI : FT.IsInvariant Q W := hWinv
    set W' : Subgroup G := W.map (Subgroup.center G).subtype with hW'def
    have hW'inv : FT.IsInvariant Q W' :=
      map_isInvariant_aux (Subgroup.center G).subtype (fun a x => rfl) hWinv
    haveI hW'invI : FT.IsInvariant Q W' := hW'inv
    have hW'leZ : W' ≤ Subgroup.center G := Subgroup.map_subtype_le W
    have hZ1leW' : H ⊓ Subgroup.center G ≤ W' := by
      have h1 : (H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G) ≤ W := by
        intro x hx
        rw [hWdef, Subgroup.mem_comap]
        have hxker : x ∈ q.ker := by rw [hqdef, QuotientGroup.ker_mk']; exact hx
        rw [MonoidHom.mem_ker.mp hxker]
        exact Wbar.one_mem
      calc H ⊓ Subgroup.center G
          = ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)).map
              (Subgroup.center G).subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
        _ ≤ W.map (Subgroup.center G).subtype := Subgroup.map_mono h1
        _ = W' := hW'def
    have hinf : H ⊓ W' = H ⊓ Subgroup.center G :=
      le_antisymm (le_inf inf_le_left (le_trans inf_le_right hW'leZ)) (le_inf inf_le_left hZ1leW')
    have hW'normal : W'.Normal := Subgroup.normal_of_le_center hW'leZ
    have hHleN : H ≤ Subgroup.normalizer (W' : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hW'normal]; exact le_top
    refine ⟨H ⊔ W', le_sup_left, inferInstance, ?_⟩
    have hrel : H.relIndex (H ⊔ W') = (H ⊓ W').relIndex W' :=
      relIndex_sup_eq_relIndex_inf_auxL hHleN
    have hZrel : (H ⊓ Subgroup.center G).relIndex W' = p := by
      have h1 := Subgroup.relIndex_map_map_of_injective
        ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)) W
        (Subgroup.subtype_injective (Subgroup.center G))
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at h1
      rw [← hW'def] at h1
      rw [h1]
      rw [show ((H ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)) = q.ker from by
        rw [hqdef, QuotientGroup.ker_mk']]
      rw [hWdef]
      rw [ker_relIndex_comap q Wbar (by
        rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)]
      exact hWbarcard
    show H.relIndex (H ⊔ W') = p
    rw [hrel, hinf]
    exact hZrel

/-! ### The requested lemma -/

/-- Auxiliary: a `Q`-invariant subgroup of `↥A` gives a subgroup of `X` normalized by `Q`. -/
theorem normalizer_map_subtype_of_isInvariant {X : Type*} [Group X] {Q A : Subgroup X}
    [FT.Normalizes Q A] {B' : Subgroup ↥A} (hB' : FT.IsInvariant ↥Q B') :
    Q ≤ Subgroup.normalizer ((B'.map A.subtype : Subgroup X) : Set X) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨(⟨q, hq⟩ : ↥Q) • a,
      (hB'.mem_smul_iff (⟨q, hq⟩ : ↥Q) a).mpr ha, rfl⟩
  · intro hy
    obtain ⟨a', ha', hval⟩ := Subgroup.mem_map.mp hy
    have hval2 : ((a' : ↥A) : X) = q * y * q⁻¹ := hval
    refine Subgroup.mem_map.mpr ⟨(⟨q, hq⟩ : ↥Q)⁻¹ • a',
      (hB'.mem_smul_iff (⟨q, hq⟩ : ↥Q)⁻¹ a').mpr ha', ?_⟩
    rw [show A.subtype ((⟨q, hq⟩ : ↥Q)⁻¹ • a')
        = q⁻¹ * ((a' : ↥A) : X) * (q⁻¹)⁻¹ from rfl, hval2]
    group

theorem exists_invariant_index_prime {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {Q A A1 : Subgroup X} (hQp : IsPGroup p Q) (hAp : IsPGroup p A)
    (hAnorm : Q ≤ Subgroup.normalizer (A : Set X))
    (hA1norm : Q ≤ Subgroup.normalizer (A1 : Set X))
    (hA1le : A1 ≤ A) (hlt : A1 < A) :
    ∃ B : Subgroup X, A1 ≤ B ∧ B ≤ A ∧
      (A1.subgroupOf B).index = p ∧ ⁅Q, B⁆ ≤ A1 := by
  haveI hNQA : FT.Normalizes Q A := ⟨hAnorm⟩
  haveI hHinv : FT.IsInvariant ↥Q (A1.subgroupOf A) := subgroupOf_isInvariant_conjAction hA1norm
  have hHlt : A1.subgroupOf A < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hlt.ne (le_antisymm hA1le h)
  obtain ⟨B', hHle, hB'inv, hidx'⟩ :=
    exists_invariant_index_prime_aux p hp hQp (Nat.card ↥A) rfl hAp (A1.subgroupOf A) hHinv hHlt
  set B : Subgroup X := B'.map A.subtype with hBdef
  have hA1B : A1 ≤ B := by
    calc A1 = (A1.subgroupOf A).map A.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA1le]
      _ ≤ B'.map A.subtype := Subgroup.map_mono hHle
      _ = B := hBdef
  have hBA : B ≤ A := Subgroup.map_subtype_le B'
  have hidxB : (A1.subgroupOf B).index = p := by
    show A1.relIndex (B'.map A.subtype) = p
    have h1 := Subgroup.relIndex_map_map_of_injective (A1.subgroupOf A) B'
      (Subgroup.subtype_injective A)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA1le] at h1
    rw [h1]
    exact hidx'
  have hQnB : Q ≤ Subgroup.normalizer (B : Set X) := by
    rw [hBdef]
    exact normalizer_map_subtype_of_isInvariant hB'inv
  exact ⟨B, hA1B, hBA, hidxB,
    commutator_le_of_index_prime_normalizer hp hQp (hAp.to_le hBA) hQnB hA1norm hA1B hidxB⟩

end Work.LocalPrelim
