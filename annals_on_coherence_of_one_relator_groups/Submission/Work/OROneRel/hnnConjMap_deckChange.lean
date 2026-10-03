import Mathlib
import Submission.Work.OROneRel.hnnConjSplit

/-!
# The deck change for the canonical HNN pair `(H, τ)`

For a group `G`, a subgroup `H ≤ G` and elements `τ = γ * σ` with `γ ∈ H`, the canonical HNN
extensions of the pairs `(H, τ)` and `(H, σ)` are isomorphic by `of ↦ of`, `t ↦ of γ⁻¹ · t`, and the
isomorphism commutes with the comparison maps `hnnConjMap`; hence the two comparison maps are
simultaneously injective.

This is the elementary observation that removes the obstruction recorded in
`Submission/Work/OROneRel/NOTES_twoLetter_hnnConjMap_freeRank2.md` §9: for the band, the opaque low
deck element `tlLowTau p q = (…).choose` may be replaced by *any* `σ` with `τ * σ⁻¹ ∈ tlH`, in
particular by one whose walk is confined to the short window `[0, p+q-1]`, after which the window
recursion `tlWin (m+1) = tlWin m ⊔ σ · tlWin m · σ⁻¹` is a statement about the crude interface
`tlLowTau_walk`/`tlLowTau_cohom` alone.
-/

namespace Work.OROneRel

universe u

variable {G : Type u} [Group G]

/-- The canonical HNN extension of the pair `(H, τ)`. -/
abbrev hnnPair (H : Subgroup G) (τ : G) : Type u :=
  HNNExtension ↥H ((hnnEdgeA H τ).subgroupOf H) ((hnnEdgeB H τ).subgroupOf H) (hnnConjEquiv H τ)

section DeckChange

/-- `hnnEdgeA` under the deck change `τ = γ * σ` with `γ ∈ H`. -/
theorem mem_hnnEdgeA_of_mul_eq {H : Subgroup G} {τ σ γ : G} (hγ : γ ∈ H) (h : τ = γ * σ)
    {a : G} (ha : a ∈ H) (hσ : σ * a * σ⁻¹ ∈ H) : τ * a * τ⁻¹ ∈ H := by
  rw [h, show (γ * σ) * a * (γ * σ)⁻¹ = γ * (σ * a * σ⁻¹) * γ⁻¹ by group]
  exact H.mul_mem (H.mul_mem hγ hσ) (H.inv_mem hγ)

/-- The converse membership: `hnnEdgeA H τ ≤ hnnEdgeA H σ` for `τ = γ * σ`, `γ ∈ H`. -/
theorem mem_mul_conj_of_mem_hnnEdgeA {H : Subgroup G} {τ σ γ : G} (hγ : γ ∈ H) (h : τ = γ * σ)
    {a : G} (ha : a ∈ H) (hτ : τ * a * τ⁻¹ ∈ H) : σ * a * σ⁻¹ ∈ H := by
  rw [show σ * a * σ⁻¹ = γ⁻¹ * (τ * a * τ⁻¹) * γ by rw [h]; group]
  exact H.mul_mem (H.mul_mem (H.inv_mem hγ) hτ) hγ

/-- **The deck change.**  If `τ = γ * σ` with `γ ∈ H`, then the canonical comparison maps of the
pairs `(H, τ)` and `(H, σ)` are simultaneously injective. -/
theorem hnnConjMap_injective_iff_mul_left {τ σ γ : G} (H : Subgroup G) (hγ : γ ∈ H)
    (h : τ = γ * σ) :
    Function.Injective (hnnConjMap H τ) ↔ Function.Injective (hnnConjMap H σ) := by
  classical
  have preimage_conj : ∀ {K : Subgroup G} (a : G), a ∈ K.map (MulAut.conj τ⁻¹) →
      τ * a * τ⁻¹ ∈ K := by
    intro K a ha
    obtain ⟨k, hk, hk2⟩ := Subgroup.mem_map.mp ha
    have hk3 : k = τ * a * τ⁻¹ := by
      change (MulAut.conj τ⁻¹ : G ≃* G) k = a at hk2
      rw [MulAut.conj_apply] at hk2; rw [← hk2]; group
    rwa [hk3] at hk
  have preimage_conjσ : ∀ {K : Subgroup G} (a : G), a ∈ K.map (MulAut.conj σ⁻¹) →
      σ * a * σ⁻¹ ∈ K := by
    intro K a ha
    obtain ⟨k, hk, hk2⟩ := Subgroup.mem_map.mp ha
    have hk3 : k = σ * a * σ⁻¹ := by
      change (MulAut.conj σ⁻¹ : G ≃* G) k = a at hk2
      rw [MulAut.conj_apply] at hk2; rw [← hk2]; group
    rwa [hk3] at hk
  have hsubτ : ∀ a : ↥H, (a : G) ∈ hnnEdgeA H σ → (a : G) ∈ hnnEdgeA H τ := by
    intro a ha
    rw [hnnEdgeA, Subgroup.mem_inf] at ha ⊢
    refine ⟨ha.1, Subgroup.mem_map.mpr ⟨τ * (a : G) * τ⁻¹,
      mem_hnnEdgeA_of_mul_eq hγ h ha.1 (preimage_conjσ (a : G) ha.2), ?_⟩⟩
    change (MulAut.conj τ⁻¹ : G ≃* G) (τ * (a : G) * τ⁻¹) = (a : G)
    rw [MulAut.conj_apply]; group
  have hsubσ : ∀ a : ↥H, (a : G) ∈ hnnEdgeA H τ → (a : G) ∈ hnnEdgeA H σ := by
    intro a ha
    rw [hnnEdgeA, Subgroup.mem_inf] at ha ⊢
    refine ⟨ha.1, Subgroup.mem_map.mpr ⟨σ * (a : G) * σ⁻¹,
      mem_mul_conj_of_mem_hnnEdgeA hγ h ha.1 (preimage_conj (a : G) ha.2), ?_⟩⟩
    change (MulAut.conj σ⁻¹ : G ≃* G) (σ * (a : G) * σ⁻¹) = (a : G)
    rw [MulAut.conj_apply]; group
  -- the coefficient identities
  have keyG1 : ∀ X : G, (γ⁻¹ : G) * (τ * X * τ⁻¹) = (σ * X * σ⁻¹) * (γ⁻¹ : G) := by
    intro X; rw [h]; group
  have keyG2 : ∀ X : G, (γ : G) * (σ * X * σ⁻¹) = (τ * X * τ⁻¹) * (γ : G) := by
    intro X; rw [h]; group
  have hkey1 : ∀ a : (hnnEdgeA H σ).subgroupOf H,
      (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) *
          (((hnnConjEquiv H τ ⟨(a : ↥H), Subgroup.mem_subgroupOf.mpr (hsubτ (a : ↥H) a.2)⟩ :
            (hnnEdgeB H τ).subgroupOf H)) : ↥H) =
        (((hnnConjEquiv H σ a : (hnnEdgeB H σ).subgroupOf H)) : ↥H) *
            (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hnnConjEquiv_coe H τ, hnnConjEquiv_coe H σ]
    exact keyG1 _
  have hkey2 : ∀ a : (hnnEdgeA H τ).subgroupOf H,
      (⟨γ, hγ⟩ : ↥H) *
          (((hnnConjEquiv H σ ⟨(a : ↥H), Subgroup.mem_subgroupOf.mpr (hsubσ (a : ↥H) a.2)⟩ :
            (hnnEdgeB H σ).subgroupOf H)) : ↥H) =
        (((hnnConjEquiv H τ a : (hnnEdgeB H τ).subgroupOf H)) : ↥H) * (⟨γ, hγ⟩ : ↥H) := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hnnConjEquiv_coe H σ, hnnConjEquiv_coe H τ]
    exact keyG2 _
  -- the two maps
  have key1 : ∀ a : (hnnEdgeA H σ).subgroupOf H,
      (HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : hnnPair H τ) * HNNExtension.t *
          (HNNExtension.of (a : ↥H) : hnnPair H τ) =
        (HNNExtension.of (((hnnConjEquiv H σ a : (hnnEdgeB H σ).subgroupOf H) : ↥H)) :
            hnnPair H τ) *
          ((HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : hnnPair H τ) * HNNExtension.t) := by
    intro a
    have hrelτ := HNNExtension.t_mul_of (A := (hnnEdgeA H τ).subgroupOf H)
      (B := (hnnEdgeB H τ).subgroupOf H) (φ := hnnConjEquiv H τ)
      (⟨(a : ↥H), Subgroup.mem_subgroupOf.mpr (hsubτ (a : ↥H) a.2)⟩ :
        (hnnEdgeA H τ).subgroupOf H)
    rw [mul_assoc, hrelτ, ← mul_assoc, ← map_mul, hkey1, map_mul, mul_assoc]
  have key2 : ∀ a : (hnnEdgeA H τ).subgroupOf H,
      (HNNExtension.of (⟨γ, hγ⟩ : ↥H) : hnnPair H σ) * HNNExtension.t *
          (HNNExtension.of (a : ↥H) : hnnPair H σ) =
        (HNNExtension.of (((hnnConjEquiv H τ a : (hnnEdgeB H τ).subgroupOf H) : ↥H)) :
            hnnPair H σ) *
          ((HNNExtension.of (⟨γ, hγ⟩ : ↥H) : hnnPair H σ) * HNNExtension.t) := by
    intro a
    have hrelσ := HNNExtension.t_mul_of (A := (hnnEdgeA H σ).subgroupOf H)
      (B := (hnnEdgeB H σ).subgroupOf H) (φ := hnnConjEquiv H σ)
      (⟨(a : ↥H), Subgroup.mem_subgroupOf.mpr (hsubσ (a : ↥H) a.2)⟩ :
        (hnnEdgeA H σ).subgroupOf H)
    rw [mul_assoc, hrelσ, ← mul_assoc, ← map_mul, hkey2, map_mul, mul_assoc]
  let Θ : hnnPair H σ →* hnnPair H τ :=
    HNNExtension.lift (HNNExtension.of (A := (hnnEdgeA H τ).subgroupOf H)
        (B := (hnnEdgeB H τ).subgroupOf H) (φ := hnnConjEquiv H τ))
      ((HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : hnnPair H τ) * HNNExtension.t) key1
  let Θ' : hnnPair H τ →* hnnPair H σ :=
    HNNExtension.lift (HNNExtension.of (A := (hnnEdgeA H σ).subgroupOf H)
        (B := (hnnEdgeB H σ).subgroupOf H) (φ := hnnConjEquiv H σ))
      ((HNNExtension.of (⟨γ, hγ⟩ : ↥H) : hnnPair H σ) * HNNExtension.t) key2
  have hcomp1 : hnnConjMap H σ = (hnnConjMap H τ).comp Θ := by
    refine HNNExtension.hom_ext ?_ ?_
    · ext h
      show (hnnConjMap H σ) (HNNExtension.of h) = (hnnConjMap H τ) (Θ (HNNExtension.of h))
      rw [show Θ (HNNExtension.of h) = HNNExtension.of h from HNNExtension.lift_of _ _ _ h]
      rw [hnnConjMap_of, hnnConjMap_of]
    · show hnnConjMap H σ HNNExtension.t = (hnnConjMap H τ) (Θ HNNExtension.t)
      rw [show Θ HNNExtension.t =
        (HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : hnnPair H τ) * HNNExtension.t
        from HNNExtension.lift_t _ _ _]
      rw [hnnConjMap_t, map_mul, hnnConjMap_of, hnnConjMap_t]
      show σ = ((⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : G) * τ
      rw [h]
      rw [← mul_assoc,
        show ((⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : G) * γ = 1 from by
          rw [show ((⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : G) = γ⁻¹ from rfl, inv_mul_cancel],
        one_mul]
  have hcomp2 : hnnConjMap H τ = (hnnConjMap H σ).comp Θ' := by
    refine HNNExtension.hom_ext ?_ ?_
    · ext h
      show (hnnConjMap H τ) (HNNExtension.of h) = (hnnConjMap H σ) (Θ' (HNNExtension.of h))
      rw [show Θ' (HNNExtension.of h) = HNNExtension.of h from HNNExtension.lift_of _ _ _ h]
      rw [hnnConjMap_of, hnnConjMap_of]
    · show hnnConjMap H τ HNNExtension.t = (hnnConjMap H σ) (Θ' HNNExtension.t)
      rw [show Θ' HNNExtension.t =
        (HNNExtension.of (⟨γ, hγ⟩ : ↥H) : hnnPair H σ) * HNNExtension.t
        from HNNExtension.lift_t _ _ _]
      rw [hnnConjMap_t, map_mul, hnnConjMap_of, hnnConjMap_t, h]
  have hid1 : Θ'.comp Θ = MonoidHom.id (hnnPair H σ) := by
    refine HNNExtension.hom_ext ?_ ?_
    · ext h
      show Θ' (Θ (HNNExtension.of h)) = HNNExtension.of h
      rw [show Θ (HNNExtension.of h) = HNNExtension.of h from HNNExtension.lift_of _ _ _ h]
      exact HNNExtension.lift_of _ _ _ h
    · show Θ' (Θ HNNExtension.t) = HNNExtension.t
      rw [show Θ HNNExtension.t =
        (HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : hnnPair H τ) * HNNExtension.t
        from HNNExtension.lift_t _ _ _]
      rw [map_mul]
      rw [show Θ' (HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H)) =
        HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) from HNNExtension.lift_of _ _ _ _]
      rw [show Θ' HNNExtension.t =
        (HNNExtension.of (⟨γ, hγ⟩ : ↥H) : hnnPair H σ) * HNNExtension.t
        from HNNExtension.lift_t _ _ _]
      rw [← mul_assoc, ← map_mul,
        show (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) * ⟨γ, hγ⟩ = 1 from by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_one]
          group,
        map_one, one_mul]
  have hid2 : Θ.comp Θ' = MonoidHom.id (hnnPair H τ) := by
    refine HNNExtension.hom_ext ?_ ?_
    · ext h
      show Θ (Θ' (HNNExtension.of h)) = HNNExtension.of h
      rw [show Θ' (HNNExtension.of h) = HNNExtension.of h from HNNExtension.lift_of _ _ _ h]
      exact HNNExtension.lift_of _ _ _ h
    · show Θ (Θ' HNNExtension.t) = HNNExtension.t
      rw [show Θ' HNNExtension.t =
        (HNNExtension.of (⟨γ, hγ⟩ : ↥H) : hnnPair H σ) * HNNExtension.t
        from HNNExtension.lift_t _ _ _]
      rw [map_mul]
      rw [show Θ (HNNExtension.of (⟨γ, hγ⟩ : ↥H)) =
        HNNExtension.of (⟨γ, hγ⟩ : ↥H) from HNNExtension.lift_of _ _ _ _]
      rw [show Θ HNNExtension.t =
        (HNNExtension.of (⟨γ⁻¹, H.inv_mem hγ⟩ : ↥H) : hnnPair H τ) * HNNExtension.t
        from HNNExtension.lift_t _ _ _]
      rw [← mul_assoc, ← map_mul,
        show (⟨γ, hγ⟩ : ↥H) * ⟨γ⁻¹, H.inv_mem hγ⟩ = 1 from by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_one]
          group,
        map_one, one_mul]
  have hinjΘ : Function.Injective Θ := by
    intro x y hxy
    have h := congrArg Θ' hxy
    rw [show Θ' (Θ x) = x from DFunLike.congr_fun hid1 x,
      show Θ' (Θ y) = y from DFunLike.congr_fun hid1 y] at h
    exact h
  have hinjΘ' : Function.Injective Θ' := by
    intro x y hxy
    have h := congrArg Θ hxy
    rw [show Θ (Θ' x) = x from DFunLike.congr_fun hid2 x,
      show Θ (Θ' y) = y from DFunLike.congr_fun hid2 y] at h
    exact h
  constructor
  · intro hinj
    rw [hcomp1]
    exact fun x y hxy => hinjΘ (hinj hxy)
  · intro hinj
    rw [hcomp2]
    exact fun x y hxy => hinjΘ' (hinj hxy)

end DeckChange

end Work.OROneRel
