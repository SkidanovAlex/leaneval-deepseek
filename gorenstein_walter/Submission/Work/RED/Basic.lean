import Submission.Work.RED.Defs

/-!
# RED: elementary API layer

Basic lemmas about the vocabulary of `Work.RED.GW2.Defs` (which is a verbatim copy of
`Submission/Work/_design_gw/Contracts2.lean`).  Everything here is elementary:
transport of the vocabulary along group isomorphisms, and the definition of
"minimal normal subgroup".
-/

namespace Work.RED.GW2

open Subgroup

variable {G : Type*} [Group G]

/-! ## Minimal normal subgroups -/

/-- `N` is a minimal normal subgroup of `G`: normal, nontrivial, and minimal among the
normal subgroups of `G` with these properties. -/
def IsMinimalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → N ≤ M

theorem IsMinimalNormal.normal {N : Subgroup G} (h : IsMinimalNormal N) : N.Normal := h.1

theorem IsMinimalNormal.ne_bot {N : Subgroup G} (h : IsMinimalNormal N) : N ≠ ⊥ := h.2.1

theorem IsMinimalNormal.eq_of_le {N M : Subgroup G} (h : IsMinimalNormal N) (hM : M.Normal)
    (hne : M ≠ ⊥) (hle : M ≤ N) : M = N :=
  le_antisymm hle (h.2.2 M hM hne hle)

/-! ## Transport of the vocabulary along `MulEquiv` -/

theorem isFourGroup_map_iff {H : Type*} [Group H] (e : G ≃* H) (V : Subgroup G) :
    IsFourGroup (V.map e.toMonoidHom) ↔ IsFourGroup V := by
  constructor
  · intro h
    refine ⟨?_, fun v hv => ?_⟩
    · rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h.1]
    · have hmem : e v ∈ (V.map e.toMonoidHom : Subgroup H) := ⟨v, hv, rfl⟩
      have h2 : (e v) ^ 2 = 1 := h.2 (e v) hmem
      rw [← map_pow, ← map_one e.toMonoidHom] at h2
      exact e.injective h2
  · intro h
    refine ⟨?_, fun v hv => ?_⟩
    · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h.1]
    · obtain ⟨w, hw, hwv⟩ := hv
      rw [← hwv, ← map_pow, h.2 w hw, map_one]

theorem centralizer_map {H : Type*} [Group H] (e : G ≃* H) (V : Subgroup G) :
    Subgroup.centralizer ((V.map e.toMonoidHom : Subgroup H) : Set H) =
      (Subgroup.centralizer (V : Set G)).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, fun v hv => ?_, rfl⟩
    have hmem : e v ∈ (V.map e.toMonoidHom : Subgroup H) := ⟨v, hv, rfl⟩
    have h2 := (mem_centralizer_iff.mp hy) (e v) hmem
    rw [← map_mul, ← map_mul] at h2
    exact e.injective h2
  · rintro ⟨x, hx, rfl⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [← map_mul, ← map_mul, hx v hv]

theorem mem_centralizer_map_iff {H : Type*} [Group H] (e : G ≃* H) (V : Subgroup G) (y : H) :
    y ∈ Subgroup.centralizer ((V.map e.toMonoidHom : Subgroup H) : Set H) ↔
      ∀ v ∈ V, y * e v = e v * y := by
  constructor
  · intro hy v hv
    exact (mem_centralizer_iff.mp hy (e v) ⟨v, hv, rfl⟩).symm
  · intro hy w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact (hy v hv).symm

theorem DShape.of_mulEquiv {Q Q' : Type*} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (h : DShape Q) (e : Q ≃* Q') : DShape Q' := by
  rcases h with h | ⟨V, hVn, hV4, hVc⟩ | ⟨h7⟩ | ⟨L, hLn, hLi, p, k, hp, hodd, h5, hL⟩
  · exact Or.inl (h.of_equiv e)
  · refine Or.inr (Or.inl ⟨V.map e.toMonoidHom, hVn.map e.toMonoidHom e.surjective, ?_, ?_⟩)
    · exact (isFourGroup_map_iff e V).2 hV4
    · rw [centralizer_map, hVc]
  · obtain ⟨h7⟩ := h7
    exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans h7⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨L.map e.toMonoidHom, hLn.map e.toMonoidHom e.surjective, ?_, p, k, hp,
      hodd, h5, ?_⟩))
    · change Odd (L.map (e : Q →* Q')).index
      rw [Subgroup.index_map_equiv L e]
      exact hLi
    · have hev := Subgroup.equivMapOfInjective L e.toMonoidHom e.injective
      rcases hL with hL | hL
      · obtain ⟨hL⟩ := hL
        exact Or.inl ⟨hev.symm.trans hL⟩
      · obtain ⟨hL⟩ := hL
        exact Or.inr ⟨hev.symm.trans hL⟩

theorem DShape.quotientBot_iff (Q : Type*) [Group Q] [Finite Q] :
    DShape (Q ⧸ (⊥ : Subgroup Q)) ↔ DShape Q :=
  ⟨fun h => h.of_mulEquiv QuotientGroup.quotientBot,
   fun h => h.of_mulEquiv QuotientGroup.quotientBot.symm⟩

theorem isDGroup_of_isPGroup_two [Finite G] (h : IsPGroup 2 G) : IsDGroup G :=
  Or.inl (h.to_quotient (oddCore G))

/-! ## Elementary facts about four-groups -/

theorem IsFourGroup.isPGroup_two {V : Subgroup G} (h : IsFourGroup V) : IsPGroup 2 V :=
  IsPGroup.of_card (n := 2) (by rw [h.1]; norm_num)

theorem IsFourGroup.nontrivial {V : Subgroup G} (h : IsFourGroup V) : Nontrivial V := by
  rw [Subgroup.nontrivial_iff_ne_bot]
  intro hbot
  have hcard := h.1
  rw [hbot] at hcard
  simp at hcard

/-! ## Minimal normal subgroups of a normal subgroup -/

/-- `K` is a minimal normal subgroup of the group `↥N` (viewed inside the ambient `G`). -/
structure IsMinimalNormalIn {G : Type*} [Group G] (N K : Subgroup G) : Prop where
  le : K ≤ N
  normal : (K.subgroupOf N).Normal
  ne_bot : K ≠ ⊥
  minimal : ∀ M : Subgroup G, M ≤ K → (M.subgroupOf N).Normal → M ≠ ⊥ → M = K

/-- The `DihedralGroup` facts that Mathlib does not have and that RED needs. -/
structure DihedralFactsProp : Prop where
  elementary_abelian_card_le_four :
    ∀ (n : ℕ) [NeZero n] (E : Subgroup (DihedralGroup n)),
      (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4
  normal_fourGroup_centralizer :
    ∀ (n : ℕ) [NeZero n] (V : Subgroup (DihedralGroup n)),
      V.Normal → IsFourGroup V → Subgroup.centralizer (V : Set (DihedralGroup n)) = V
  fourGroup_exists_of_even :
    ∀ (n : ℕ) [NeZero n], Even n → ∃ V : Subgroup (DihedralGroup n), IsFourGroup V
  involution_ne_of_central :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ z : DihedralGroup n, orderOf z = 2 →
      z ∈ Subgroup.center (DihedralGroup n) →
        ∃ u : DihedralGroup n, orderOf u = 2 ∧ u ≠ z

/-- Facts about minimal normal subgroups (Bender's `O(G) = 1` analysis). -/
structure MinimalNormalFactsProp : Prop where
  exists_minimal :
    ∀ (G : Type) [Group G] [Finite G] [Nontrivial G], ∃ N : Subgroup G, IsMinimalNormal N
  exists_minimalIn :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N ≠ ⊥ →
      ∃ K : Subgroup G, IsMinimalNormalIn N K
  char_free :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), IsMinimalNormal N →
      ∀ H : Subgroup G, H ≤ N → (H.subgroupOf N).Characteristic → H = ⊥ ∨ H = N
  char_normal :
    ∀ (G : Type) [Group G] [Finite G] (N K H : Subgroup G), IsMinimalNormal N →
      H ≤ K → K ≤ N → (K.subgroupOf N).Normal → (H.subgroupOf K).Characteristic →
        (H.subgroupOf N).Normal
  commute_of_minimalNormalIn :
    ∀ (G : Type) [Group G] [Finite G] (N K K' : Subgroup G), IsMinimalNormal N →
      IsMinimalNormalIn N K → IsMinimalNormalIn N K' → K ≠ K' →
        K ⊓ K' = ⊥ ∧ ∀ x ∈ K, ∀ y ∈ K', x * y = y * x
  abelian_elementary :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), IsMinimalNormal N →
      IsMulCommutative N → ∃ p : ℕ, p.Prime ∧ ∀ x ∈ N, x ^ p = 1
  nonabelian_of_minimalNormalIn :
    ∀ (G : Type) [Group G] [Finite G] (N K : Subgroup G), IsMinimalNormal N →
      IsMinimalNormalIn N K → ¬ IsMulCommutative N → ¬ IsMulCommutative K
  isSimpleGroup_of_minimalNormalIn_self :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), IsMinimalNormalIn N N →
      IsSimpleGroup ↥N

/-- The inner automorphism group facts. -/
structure AutInnFactsProp : Prop where
  inn_normal : ∀ (N : Type*) [Group N], (MonoidHom.range (MulAut.conj : N →* MulAut N)).Normal
  centralizer_inn :
    ∀ (N : Type*) [Group N],
      Subgroup.centralizer (MonoidHom.range (MulAut.conj : N →* MulAut N) :
        Set (MulAut N)) = ⊥
  innMulEquiv : ∀ (N : Type*) [Group N], Subgroup.center N = ⊥ →
    Nonempty (N ≃* MonoidHom.range (MulAut.conj : N →* MulAut N))

/-- The `oddCore` (`O(G)`) API. -/
structure OddCoreFactsProp : Prop where
  characteristic : ∀ (G : Type) [Group G], (oddCore G).Characteristic
  odd : ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card (oddCore G))
  le_oddCore : ∀ (G : Type) [Group G] (N : Subgroup G), N.Normal → Odd (Nat.card N) →
    N ≤ oddCore G
  eq_top_of_odd : ∀ (G : Type) [Group G], Odd (Nat.card G) → oddCore G = ⊤
  le_of_normal : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), K.Normal →
    (oddCore K).map K.subtype ≤ oddCore G
  quotient_eq_bot : ∀ (G : Type) [Group G] [Finite G], oddCore (G ⧸ oddCore G) = ⊥
  card_quotient_lt : ∀ (G : Type) [Group G] [Finite G], oddCore G ≠ ⊥ →
    Nat.card (G ⧸ oddCore G) < Nat.card G


/-! ## Helper lemmas -/

theorem isCyclic_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) [IsCyclic G] :
    IsCyclic H := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := G)
  exact ⟨e g, fun y => by
    obtain ⟨k, hk⟩ := hg (e.symm y)
    exact ⟨k, by
      rw [← e.apply_symm_apply y, ← hk]
      exact (map_zpow e.toMonoidHom g k).symm⟩⟩

theorem neZero_of_mulEquiv_dihedral {H : Type*} [Group H] [Finite H] {n : ℕ}
    (e : H ≃* DihedralGroup n) : NeZero n := by
  refine ⟨fun hn => ?_⟩
  subst hn
  haveI : Finite (DihedralGroup 0) := Finite.of_injective e.symm e.symm.injective
  exact (inferInstance : Infinite (DihedralGroup 0)).not_finite this

end Work.RED.GW2
namespace Work.RED.GW2

/-- Every fact that the RED area consumes from elsewhere, bundled.

`dihedralSubgroup`/`dih` are the `DihedralGroup` library, `min` the minimal-normal-subgroup
structure theory, `odd` the `O(G)` API, `ft` Feit–Thompson, `csq` Burnside's normal
2-complement in the cyclic-Sylow case, and the remaining fields are the small lemmas that
the case analysis of blueprint §4 uses (`NOTES_RED.md`). -/
structure RedFacts : Prop where
  dihedralSubgroup : ∀ (n : ℕ) [NeZero n] (H : Subgroup (DihedralGroup n)),
    IsCyclic ↥H ∨ ∃ m : ℕ, Nonempty (↥H ≃* DihedralGroup m)
  dih : DihedralFactsProp
  min : MinimalNormalFactsProp
  odd : OddCoreFactsProp
  ft : FeitThompsonProp
  csq : ∀ (G : Type) [Group G] [Finite G] (P : Sylow 2 G),
    IsCyclic ↥(P : Subgroup G) → IsPGroup 2 (G ⧸ oddCore G)
  dcs : ∀ {G : Type} [Group G] [Finite G] (K : Subgroup G),
    DihOrCycSylow G → DihOrCycSylow ↥K
  diiso : ∀ {G H : Type} [Group G] [Finite G] [Group H] [Finite H],
    DihOrCycSylow G → G ≃* H → DihOrCycSylow H
  quotSylow : ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card (oddCore G)) →
    DihOrCycSylow G → DihOrCycSylow (G ⧸ oddCore G)
  cent2 : ∀ {G : Type} [Group G] (N : Subgroup G), N.Normal → Nat.card N = 2 →
    N ≤ Subgroup.center G
  cent4 : ∀ {G : Type} [Group G] [Finite G] (N : Subgroup G), N.Normal →
    Subgroup.center ↥N = ⊥ →
    ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G}, (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n →
    (∃ V : Subgroup G, V ≤ N ∧ IsFourGroup V) →
    Odd (Nat.card (Subgroup.centralizer (N : Set G)))
  v4 : ∀ (N : Type) [Group N] [Finite N], DihOrCycSylow N → oddCore N = ⊥ →
    ¬ Group.IsSolvable N → ∃ V : Subgroup N, IsFourGroup V
  fourNorm : ∀ {G : Type} [Group G] [Finite G] {N : Subgroup G}, N.Normal → IsFourGroup N →
    oddCore G = ⊥ →
    ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G}, (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n →
    Subgroup.centralizer (N : Set G) = N
  notSol : ∀ {G : Type} [Group G] [Finite G] {N K : Subgroup G}, IsMinimalNormal N →
    IsMinimalNormalIn N K → ¬ IsMulCommutative K → ¬ Group.IsSolvable ↥K
  oddCoreK : ∀ {G : Type} [Group G] [Finite G] {N K : Subgroup G}, IsMinimalNormal N →
    IsMinimalNormalIn N K → ¬ Group.IsSolvable ↥K → oddCore ↥K = ⊥
  eqOfContained : ∀ {G : Type} [Group G] [Finite G] (N K : Subgroup G),
    IsMinimalNormal N → IsMinimalNormalIn N K →
    (∃ V : Subgroup G, V ≤ K ∧ IsFourGroup V) →
    ∀ {n : ℕ} [NeZero n] {P : Sylow 2 G}, (↥(P : Subgroup G) ≃* DihedralGroup n) → 2 ≤ n →
    K = N

end Work.RED.GW2
