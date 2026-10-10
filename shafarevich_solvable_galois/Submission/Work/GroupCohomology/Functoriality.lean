import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Actions
import Submission.Work.GroupCohomology.H1_induction_on
import Submission.Work.GroupCohomology.H2_induction_on
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.GroupCohomology

variable (G : Type u) {A : Type v} {B : Type w} [Group G]
variable [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]

/-! ## Maps on cochains -/

/-- The map `C¹(G, A) → C¹(G, B)` induced by an additive map `φ : A →+ B`. -/
def mapCochain1 (φ : A →+ B) : (G → A) →+ (G → B) where
  toFun f := fun g => φ (f g)
  map_zero' := by funext g; simp
  map_add' f f' := by funext g; simp [map_add]

/-- The map `C²(G, A) → C²(G, B)` induced by an additive map `φ : A →+ B`. -/
def mapCochain2 (φ : A →+ B) : (G × G → A) →+ (G × G → B) where
  toFun f := fun g => φ (f g)
  map_zero' := by funext g; simp
  map_add' f f' := by funext g; simp [map_add]

/-- The map `C³(G, A) → C³(G, B)` induced by an additive map `φ : A →+ B`. -/
def mapCochain3 (φ : A →+ B) : (G × G × G → A) →+ (G × G × G → B) where
  toFun f := fun g => φ (f g)
  map_zero' := by funext g; simp
  map_add' f f' := by funext g; simp [map_add]

@[simp] theorem mapCochain1_apply (φ : A →+ B) (f : G → A) (g : G) :
    mapCochain1 G φ f g = φ (f g) := rfl

@[simp] theorem mapCochain2_apply (φ : A →+ B) (f : G × G → A) (g : G × G) :
    mapCochain2 G φ f g = φ (f g) := rfl

@[simp] theorem mapCochain3_apply (φ : A →+ B) (f : G × G × G → A) (g : G × G × G) :
    mapCochain3 G φ f g = φ (f g) := rfl

/-- An additive map of `G`-modules is *equivariant* if it commutes with the action of `G`. -/
def IsEquivariant (φ : A →+ B) : Prop := ∀ (g : G) (a : A), φ (g • a) = g • φ a

variable {G}

theorem IsEquivariant.comp {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    {φ : A →+ B} {ψ : B →+ C} (hψ : IsEquivariant G ψ) (hφ : IsEquivariant G φ) :
    IsEquivariant G (ψ.comp φ) := fun g a => by
  simp only [AddMonoidHom.comp_apply, hφ g a, hψ g (φ a)]

theorem isEquivariant_id : IsEquivariant G (AddMonoidHom.id A) := fun _ _ => rfl

theorem isEquivariant_zero : IsEquivariant G (0 : A →+ B) := fun _ _ => by simp

theorem isEquivariant_add {φ ψ : A →+ B} (hφ : IsEquivariant G φ) (hψ : IsEquivariant G ψ) :
    IsEquivariant G (φ + ψ) := fun g a => by
  simp only [AddMonoidHom.add_apply, hφ g a, hψ g a, smul_add]

variable (G)

theorem mapCochain1_d0 (φ : A →+ B) (hφ : IsEquivariant G φ) (a : A) :
    mapCochain1 G φ (d0 G A a) = d0 G B (φ a) := by
  funext g
  simp only [mapCochain1_apply, d0_apply, map_sub, hφ g a]

theorem mapCochain2_d1 (φ : A →+ B) (hφ : IsEquivariant G φ) (f : G → A) :
    mapCochain2 G φ (d1 G A f) = d1 G B (mapCochain1 G φ f) := by
  funext g
  obtain ⟨g₁, g₂⟩ := g
  simp only [mapCochain2_apply, mapCochain1_apply, d1_apply, map_add, map_sub, hφ g₁ (f g₂)]

theorem mapCochain3_d2 (φ : A →+ B) (hφ : IsEquivariant G φ) (c : G × G → A) :
    mapCochain3 G φ (d2 G A c) = d2 G B (mapCochain2 G φ c) := by
  funext g
  obtain ⟨g₁, g₂, g₃⟩ := g
  simp only [mapCochain3_apply, mapCochain2_apply, d2_apply, map_add, map_sub, hφ g₁ (c (g₂, g₃))]

/-! ## Maps on cocycles -/

/-- The map `Z¹(G, A) → Z¹(G, B)` induced by an equivariant additive map. -/
def mapZ1 (φ : A →+ B) (hφ : IsEquivariant G φ) : Z1 G A →+ Z1 G B where
  toFun f := ⟨mapCochain1 G φ f, by
    rw [mem_Z1_iff]
    intro g h
    simp only [mapCochain1_apply]
    rw [f.2 g h, map_add, hφ]⟩
  map_zero' := by ext g; simp
  map_add' f f' := by ext g; simp [map_add]

/-- The map `Z²(G, A) → Z²(G, B)` induced by an equivariant additive map. -/
def mapZ2 (φ : A →+ B) (hφ : IsEquivariant G φ) : Z2 G A →+ Z2 G B where
  toFun c := ⟨mapCochain2 G φ c, by
    rw [mem_Z2_iff]
    intro g h k
    simp only [mapCochain2_apply]
    rw [← map_add, c.2 g h k, map_add, hφ]⟩
  map_zero' := by ext g; simp
  map_add' c c' := by ext g; simp [map_add]

@[simp] theorem mapZ1_coe (φ : A →+ B) (hφ : IsEquivariant G φ) (f : Z1 G A) :
    ((mapZ1 G φ hφ f : Z1 G B) : G → B) = mapCochain1 G φ (f : G → A) := rfl

@[simp] theorem mapZ2_coe (φ : A →+ B) (hφ : IsEquivariant G φ) (c : Z2 G A) :
    ((mapZ2 G φ hφ c : Z2 G B) : G × G → B) = mapCochain2 G φ (c : G × G → A) := rfl

theorem mapCochain1_mem_B1 (φ : A →+ B) (hφ : IsEquivariant G φ) {f : G → A}
    (hf : f ∈ B1 G A) : mapCochain1 G φ f ∈ B1 G B := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨φ a, (mapCochain1_d0 G φ hφ a).symm⟩

theorem mapCochain2_mem_B2 (φ : A →+ B) (hφ : IsEquivariant G φ) {c : G × G → A}
    (hc : c ∈ B2 G A) : mapCochain2 G φ c ∈ B2 G B := by
  obtain ⟨f, rfl⟩ := hc
  exact ⟨mapCochain1 G φ f, (mapCochain2_d1 G φ hφ f).symm⟩

/-! ## Maps on cohomology -/

/-- The map `H¹(G, A) → H¹(G, B)` induced by an equivariant additive map. -/
noncomputable def mapH1 (φ : A →+ B) (hφ : IsEquivariant G φ) : H1 G A →+ H1 G B :=
  QuotientAddGroup.lift ((B1 G A).comap (Z1 G A).subtype)
    ((H1π G B).comp (mapZ1 G φ hφ)) (by
      intro x hx
      have hx' : ((x : Z1 G A) : G → A) ∈ B1 G A := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      have hy : ((mapZ1 G φ hφ x : Z1 G B) : G → B) ∈ B1 G B := by
        simpa using mapCochain1_mem_B1 G φ hφ hx'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hy)

/-- The map `H²(G, A) → H²(G, B)` induced by an equivariant additive map. -/
noncomputable def mapH2 (φ : A →+ B) (hφ : IsEquivariant G φ) : H2 G A →+ H2 G B :=
  QuotientAddGroup.lift ((B2 G A).comap (Z2 G A).subtype)
    ((H2π G B).comp (mapZ2 G φ hφ)) (by
      intro x hx
      have hx' : ((x : Z2 G A) : G × G → A) ∈ B2 G A := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      have hy : ((mapZ2 G φ hφ x : Z2 G B) : G × G → B) ∈ B2 G B := by
        simpa using mapCochain2_mem_B2 G φ hφ hx'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H2π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hy)

theorem mapH1_H1π (φ : A →+ B) (hφ : IsEquivariant G φ) (f : Z1 G A) :
    mapH1 G φ hφ (H1π G A f) = H1π G B (mapZ1 G φ hφ f) :=
  QuotientAddGroup.lift_mk' _ _ f

theorem mapH2_H2π (φ : A →+ B) (hφ : IsEquivariant G φ) (c : Z2 G A) :
    mapH2 G φ hφ (H2π G A c) = H2π G B (mapZ2 G φ hφ c) :=
  QuotientAddGroup.lift_mk' _ _ c

/-! ## Restriction to a subgroup -/

section Restriction

variable (H : Subgroup G)

/-- Restriction of `1`-cochains to a subgroup. -/
def resCochain1 : (G → A) →+ (H → A) where
  toFun f := fun h => f h
  map_zero' := rfl
  map_add' f f' := rfl

/-- Restriction of `2`-cochains to a subgroup. -/
def resCochain2 : (G × G → A) →+ (H × H → A) where
  toFun f := fun h => f (h.1, h.2)
  map_zero' := rfl
  map_add' f f' := rfl

@[simp] theorem resCochain1_apply (f : G → A) (h : H) : resCochain1 G H f h = f h := rfl

@[simp] theorem resCochain2_apply (f : G × G → A) (h : H × H) :
    resCochain2 G H f h = f (h.1, h.2) := rfl

/-- Restriction of `1`-cocycles to a subgroup. -/
def resZ1 : Z1 G A →+ Z1 H A where
  toFun f := ⟨resCochain1 G H (f : G → A), by
    rw [mem_Z1_iff]
    intro x y
    exact f.2 (x : G) (y : G)⟩
  map_zero' := by ext h; simp
  map_add' f f' := by ext h; simp

/-- Restriction of `2`-cocycles to a subgroup. -/
def resZ2 : Z2 G A →+ Z2 H A where
  toFun c := ⟨resCochain2 G H (c : G × G → A), by
    rw [mem_Z2_iff]
    intro x y z
    exact c.2 (x : G) (y : G) (z : G)⟩
  map_zero' := by ext h; simp
  map_add' c c' := by ext h; simp

@[simp] theorem resZ1_coe (f : Z1 G A) :
    ((resZ1 G H f : Z1 H A) : H → A) = resCochain1 G H (f : G → A) := rfl

@[simp] theorem resZ2_coe (c : Z2 G A) :
    ((resZ2 G H c : Z2 H A) : H × H → A) = resCochain2 G H (c : G × G → A) := rfl

theorem resCochain1_d0 (a : A) : resCochain1 G H (d0 G A a) = d0 H A a := rfl

theorem resCochain2_d1 (f : G → A) :
    resCochain2 G H (d1 G A f) = d1 H A (resCochain1 G H f) := rfl

theorem resCochain1_mem_B1 {f : G → A} (hf : f ∈ B1 G A) : resCochain1 G H f ∈ B1 H A := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a, (resCochain1_d0 G H a).symm⟩

theorem resCochain2_mem_B2 {c : G × G → A} (hc : c ∈ B2 G A) : resCochain2 G H c ∈ B2 H A := by
  obtain ⟨f, rfl⟩ := hc
  exact ⟨resCochain1 G H f, (resCochain2_d1 G H f).symm⟩

/-- Restriction `H¹(G, A) → H¹(H, A)` for a subgroup `H ≤ G`. -/
noncomputable def resH1 : H1 G A →+ H1 H A :=
  QuotientAddGroup.lift ((B1 G A).comap (Z1 G A).subtype) ((H1π H A).comp (resZ1 G H)) (by
    intro x hx
    have hx' : ((x : Z1 G A) : G → A) ∈ B1 G A := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    have hy : ((resZ1 G H x : Z1 H A) : H → A) ∈ B1 H A := by
      simpa using resCochain1_mem_B1 G H hx'
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
    exact hy)

/-- Restriction `H²(G, A) → H²(H, A)` for a subgroup `H ≤ G`. -/
noncomputable def resH2 : H2 G A →+ H2 H A :=
  QuotientAddGroup.lift ((B2 G A).comap (Z2 G A).subtype) ((H2π H A).comp (resZ2 G H)) (by
    intro x hx
    have hx' : ((x : Z2 G A) : G × G → A) ∈ B2 G A := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    have hy : ((resZ2 G H x : Z2 H A) : H × H → A) ∈ B2 H A := by
      simpa using resCochain2_mem_B2 G H hx'
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H2π, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
    exact hy)

theorem resH1_H1π (f : Z1 G A) : resH1 G H (H1π G A f) = H1π H A (resZ1 G H f) :=
  QuotientAddGroup.lift_mk' _ _ f

theorem resH2_H2π (c : Z2 G A) : resH2 G H (H2π G A c) = H2π H A (resZ2 G H c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Restriction

/-! ## Functoriality laws -/

theorem mapZ1_id : mapZ1 G (AddMonoidHom.id A) (isEquivariant_id (G := G) (A := A)) =
    AddMonoidHom.id (↥(Z1 G A)) := by
  ext f
  rfl

theorem mapZ2_id : mapZ2 G (AddMonoidHom.id A) (isEquivariant_id (G := G) (A := A)) =
    AddMonoidHom.id (↥(Z2 G A)) := by
  ext f
  rfl

theorem mapZ1_zero : mapZ1 G (0 : A →+ B) (isEquivariant_zero (G := G) (A := A) (B := B)) = 0 := by
  ext f
  rfl

theorem mapZ2_zero : mapZ2 G (0 : A →+ B) (isEquivariant_zero (G := G) (A := A) (B := B)) = 0 := by
  ext f
  rfl

theorem mapH1_id : mapH1 G (AddMonoidHom.id A) (isEquivariant_id (G := G) (A := A)) =
    AddMonoidHom.id (H1 G A) := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H1_induction_on with
  | h f => rw [mapH1_H1π, mapZ1_id]; rfl

theorem mapH2_id : mapH2 G (AddMonoidHom.id A) (isEquivariant_id (G := G) (A := A)) =
    AddMonoidHom.id (H2 G A) := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H2_induction_on with
  | h c => rw [mapH2_H2π, mapZ2_id]; rfl

theorem mapH1_zero : mapH1 G (0 : A →+ B) (isEquivariant_zero (G := G) (A := A) (B := B)) = 0 := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H1_induction_on with
  | h f => rw [mapH1_H1π, mapZ1_zero]; rfl

theorem mapH2_zero : mapH2 G (0 : A →+ B) (isEquivariant_zero (G := G) (A := A) (B := B)) = 0 := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H2_induction_on with
  | h c => rw [mapH2_H2π, mapZ2_zero]; rfl

section Comp

variable {C : Type x} [AddCommGroup C] [DistribMulAction G C]

theorem mapZ1_comp (φ : A →+ B) (ψ : B →+ C) (hφ : IsEquivariant G φ) (hψ : IsEquivariant G ψ) :
    mapZ1 G (ψ.comp φ) (hψ.comp hφ) = (mapZ1 G ψ hψ).comp (mapZ1 G φ hφ) := by
  ext f
  rfl

theorem mapZ2_comp (φ : A →+ B) (ψ : B →+ C) (hφ : IsEquivariant G φ) (hψ : IsEquivariant G ψ) :
    mapZ2 G (ψ.comp φ) (hψ.comp hφ) = (mapZ2 G ψ hψ).comp (mapZ2 G φ hφ) := by
  ext f
  rfl

theorem mapH1_comp (φ : A →+ B) (ψ : B →+ C) (hφ : IsEquivariant G φ) (hψ : IsEquivariant G ψ) :
    mapH1 G (ψ.comp φ) (hψ.comp hφ) = (mapH1 G ψ hψ).comp (mapH1 G φ hφ) := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H1_induction_on with
  | h f =>
    rw [mapH1_H1π, AddMonoidHom.comp_apply, mapH1_H1π, mapH1_H1π]
    congr 1

theorem mapH2_comp (φ : A →+ B) (ψ : B →+ C) (hφ : IsEquivariant G φ) (hψ : IsEquivariant G ψ) :
    mapH2 G (ψ.comp φ) (hψ.comp hφ) = (mapH2 G ψ hψ).comp (mapH2 G φ hφ) := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H2_induction_on with
  | h c =>
    rw [mapH2_H2π, AddMonoidHom.comp_apply, mapH2_H2π, mapH2_H2π]
    congr 1

end Comp

end Work.GroupCohomology
