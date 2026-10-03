import Mathlib

/-!
# The canonical HNN decomposition attached to a pair `(H, τ)`

This file is part of the subproject `OROneRel`.  For a subgroup `H ≤ G` and an element `τ ∈ G` it
provides

* `hnnEdgeA H τ = H ⊓ τ⁻¹Hτ`, the largest subgroup of `H` whose `τ`-conjugate still lies in `H`,
  and `hnnEdgeB H τ = τ · (hnnEdgeA H τ) · τ⁻¹ ≤ H`;
* the conjugation isomorphism `hnnConjEquiv : A ≃* B`;
* the canonical comparison map `hnnConjMap : HNN(↥H, A, B, φ) →* G` with `of ↦ incl` and `t ↦ τ`;
* the criterion `hnnConjMap_bijective`: if `hnnConjMap` is injective and `H` together with `τ`
  generates `G`, then it is an isomorphism.

The point is that this isolates *all* of the bookkeeping of the HNN decomposition of a group over a
subgroup: the only remaining input for such a decomposition is the injectivity of `hnnConjMap`, a
single statement about the pair `(H, τ)` (the Britton/normal-form input).
-/

namespace Work.OROneRel

universe u

variable {G : Type u} [Group G]

/-- `A = H ⊓ τ⁻¹Hτ`: the largest subgroup of `H` whose `τ`-conjugate still lies in `H`. -/
def hnnEdgeA (H : Subgroup G) (τ : G) : Subgroup G := H ⊓ H.map (MulAut.conj τ⁻¹)

/-- `B = τ A τ⁻¹`. -/
def hnnEdgeB (H : Subgroup G) (τ : G) : Subgroup G := (hnnEdgeA H τ).map (MulAut.conj τ)

theorem hnnEdgeA_le (H : Subgroup G) (τ : G) : hnnEdgeA H τ ≤ H :=
  fun _ hx => (Subgroup.mem_inf.mp hx).1

theorem hnnEdgeB_le (H : Subgroup G) (τ : G) : hnnEdgeB H τ ≤ H := by
  intro b hb
  rw [hnnEdgeB, Subgroup.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have ha' : a ∈ H.map (MulAut.conj τ⁻¹) := (Subgroup.mem_inf.mp ha).2
  rw [Subgroup.mem_map] at ha'
  obtain ⟨h, hh, hhe⟩ := ha'
  rw [← hhe]
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- The underlying function of the conjugation isomorphism `A → B`. -/
def hnnConjFun (H : Subgroup G) (τ : G) (a : (hnnEdgeA H τ).subgroupOf H) :
    (hnnEdgeB H τ).subgroupOf H :=
  ⟨⟨τ * (a : G) * τ⁻¹,
      hnnEdgeB_le H τ (Subgroup.mem_map.mpr ⟨(a : G), a.2, by simp [MulAut.conj_apply]⟩)⟩,
    Subgroup.mem_map.mpr ⟨(a : G), a.2, by simp [MulAut.conj_apply]⟩⟩

@[simp] theorem hnnConjFun_coe (H : Subgroup G) (τ : G)
    (a : (hnnEdgeA H τ).subgroupOf H) :
    ((hnnConjFun H τ a : (hnnEdgeB H τ).subgroupOf H) : G) = τ * (a : G) * τ⁻¹ :=
  rfl

/-- The membership underlying the inverse function. -/
theorem hnnConjFunInv_mem (H : Subgroup G) (τ : G) (b : (hnnEdgeB H τ).subgroupOf H) :
    τ⁻¹ * (b : G) * τ ∈ hnnEdgeA H τ := by
  obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp (b.2 : (b : G) ∈ hnnEdgeB H τ)
  have h1 : (MulAut.conj τ) c = ((b : (hnnEdgeB H τ).subgroupOf H) : G) := hcb
  rw [MulAut.conj_apply] at h1
  have key : τ⁻¹ * ((b : (hnnEdgeB H τ).subgroupOf H) : G) * τ = c := by
    rw [← h1]; group
  rw [key]
  exact hc

/-- The inverse of the underlying function. -/
def hnnConjFunInv (H : Subgroup G) (τ : G) (b : (hnnEdgeB H τ).subgroupOf H) :
    (hnnEdgeA H τ).subgroupOf H :=
  ⟨⟨τ⁻¹ * (b : G) * τ, hnnEdgeA_le H τ (hnnConjFunInv_mem H τ b)⟩, hnnConjFunInv_mem H τ b⟩

/-- The conjugation isomorphism `A ≃* B` between the two associated subgroups of `H`. -/
noncomputable def hnnConjEquiv (H : Subgroup G) (τ : G) :
    (hnnEdgeA H τ).subgroupOf H ≃* (hnnEdgeB H τ).subgroupOf H where
  toFun := hnnConjFun H τ
  invFun := hnnConjFunInv H τ
  left_inv a := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [hnnConjFunInv, hnnConjFun, Subgroup.coe_mul]
    group
  right_inv b := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [hnnConjFunInv, hnnConjFun, Subgroup.coe_mul]
    group
  map_mul' a a' := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [hnnConjFun, Subgroup.coe_mul]
    group

/-- The value of the conjugation isomorphism on the underlying elements of `G`. -/
theorem hnnConjEquiv_coe (H : Subgroup G) (τ : G)
    (a : (hnnEdgeA H τ).subgroupOf H) :
    ((hnnConjEquiv H τ a : (hnnEdgeB H τ).subgroupOf H) : G) = τ * (a : G) * τ⁻¹ :=
  hnnConjFun_coe H τ a

/-- **The canonical comparison map** `HNN(↥H, A, B, φ) →* G`, sending the base inclusion to itself
and the stable letter to `τ`.  Its well definedness is the fact that `φ` is *defined* by conjugation
by `τ`: for `a ∈ A` one has `τ * ↑a = ↑(φ a) * τ` by `hnnConjEquiv_coe`. -/
noncomputable def hnnConjMap (H : Subgroup G) (τ : G) :
    HNNExtension ↥H ((hnnEdgeA H τ).subgroupOf H) ((hnnEdgeB H τ).subgroupOf H)
      (hnnConjEquiv H τ) →* G :=
  HNNExtension.lift H.subtype τ (by
    intro a
    have h : H.subtype (hnnConjEquiv H τ a) = τ * (a : G) * τ⁻¹ := hnnConjEquiv_coe H τ a
    have h2 : H.subtype ↑a = ((a : (hnnEdgeA H τ).subgroupOf H) : G) := rfl
    rw [h, h2]
    group)

@[simp] theorem hnnConjMap_of (H : Subgroup G) (τ : G) (h : ↥H) :
    hnnConjMap H τ (HNNExtension.of h) = (h : G) :=
  HNNExtension.lift_of _ _ _ h

@[simp] theorem hnnConjMap_t (H : Subgroup G) (τ : G) :
    hnnConjMap H τ HNNExtension.t = τ :=
  HNNExtension.lift_t _ _ _

/-- **The criterion.**  If the canonical comparison map is injective and `H` together with `τ`
generates `G`, then it is an isomorphism (hence `G ≅ HNN(↥H, A, B, φ)`). -/
theorem hnnConjMap_bijective (H : Subgroup G) (τ : G)
    (hinj : Function.Injective (hnnConjMap H τ))
    (hgen : H ⊔ Subgroup.closure {τ} = ⊤) :
    Function.Bijective (hnnConjMap H τ) := by
  refine ⟨hinj, ?_⟩
  have hle : (⊤ : Subgroup G) ≤ (hnnConjMap H τ).range := by
    rw [← hgen]
    apply sup_le
    · intro h hh
      exact ⟨HNNExtension.of ⟨h, hh⟩, by simp⟩
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨HNNExtension.t, by simp⟩
  intro y
  exact hle (Subgroup.mem_top y)

end Work.OROneRel
