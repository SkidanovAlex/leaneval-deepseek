/-
Copyright: the martinet_totally_real_towers team.

# Elementary API for `Work.ConCohomology`

This module collects the basic computations on the inhomogeneous differentials of
`Submission.Work.ConCohomology.Defs`, together with the definition of an equivariant additive map
of coefficient modules (`EqHom`) and of a continuous additive homomorphism `G → M`
(`ContAddHom`).
-/

import Submission.Work.ConCohomology.Defs

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function

/-! ### Equivariant additive maps of coefficient modules -/

/-- A `G`-equivariant additive map between two discrete coefficient modules. -/
structure EqHom (G : Type*) [Group G] (A : Type*) (B : Type*) [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] extends A →+ B where
  map_smul' : ∀ (σ : G) (a : A), toAddMonoidHom (σ • a) = σ • toAddMonoidHom a

namespace EqHom

variable {G : Type*} [Group G] {A B C : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

instance instCoeFunEqHom : CoeFun (EqHom G A B) (fun _ => A → B) :=
  ⟨fun F => F.toAddMonoidHom⟩

@[simp] lemma map_zero (F : EqHom G A B) : F 0 = 0 := F.toAddMonoidHom.map_zero

@[simp] lemma map_add (F : EqHom G A B) (a b : A) : F (a + b) = F a + F b :=
  F.toAddMonoidHom.map_add a b

@[simp] lemma map_neg (F : EqHom G A B) (a : A) : F (-a) = -F a := F.toAddMonoidHom.map_neg a

@[simp] lemma map_sub (F : EqHom G A B) (a b : A) : F (a - b) = F a - F b :=
  F.toAddMonoidHom.map_sub a b

@[simp] lemma map_smul (F : EqHom G A B) (σ : G) (a : A) : F (σ • a) = σ • F a :=
  F.map_smul' σ a

@[ext] lemma ext {F F' : EqHom G A B} (h : ∀ a, F a = F' a) : F = F' := by
  cases F; cases F'
  congr
  ext a
  exact h a

/-- The identity equivariant map. -/
def id (G : Type*) [Group G] (A : Type*) [AddCommGroup A] [DistribMulAction G A] :
    EqHom G A A where
  toAddMonoidHom := AddMonoidHom.id A
  map_smul' := fun _ _ => rfl

/-- Composition of equivariant maps. -/
def comp (F : EqHom G B C) (F' : EqHom G A B) : EqHom G A C where
  toAddMonoidHom := F.toAddMonoidHom.comp F'.toAddMonoidHom
  map_smul' σ a := by
    show F.toAddMonoidHom.comp F'.toAddMonoidHom (σ • a) =
      σ • F.toAddMonoidHom.comp F'.toAddMonoidHom a
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, F'.map_smul, F.map_smul]

@[simp] lemma comp_apply (F : EqHom G B C) (F' : EqHom G A B) (a : A) :
    F.comp F' a = F (F' a) := rfl

@[simp] lemma id_apply (a : A) : id G A a = a := rfl

@[simp] lemma comp_id (F : EqHom G A B) : F.comp (id G A) = F := rfl

@[simp] lemma id_comp (F : EqHom G A B) : (id G B).comp F = F := rfl

end EqHom

/-! ### The differentials commute with equivariant coefficient maps -/

section Comp

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [DistribMulAction G A] [DistribMulAction G B]

/-- The zeroth differential commutes with an equivariant coefficient map. -/
lemma d0Fun_comp (F : EqHom G A B) (a : A) :
    d0Fun (G := G) (F a) = fun σ => F (d0Fun (G := G) a σ) := by
  funext σ
  simp [d0Fun]

/-- The first differential commutes with an equivariant coefficient map. -/
lemma d1Fun_comp (F : EqHom G A B) (h : G → A) :
    d1Fun (G := G) (fun σ => F (h σ)) = fun p => F (d1Fun (G := G) h p) := by
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Fun_apply]
  rw [map_add, map_sub, EqHom.map_smul]

/-- The second differential commutes with an equivariant coefficient map. -/
lemma d2Fun_comp (F : EqHom G A B) (h : G × G → A) :
    d2Fun (G := G) (fun p => F (h p)) = fun p => F (d2Fun (G := G) h p) := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply]
  rw [map_sub, map_add, map_sub, EqHom.map_smul]

lemma IsCocycle1.comp {f : G → A} (hf : IsCocycle1 f) (F : EqHom G A B) :
    IsCocycle1 (fun σ => F (f σ)) := by
  rw [isCocycle1_iff_d1Fun] at hf ⊢
  rw [d1Fun_comp, hf]
  funext p
  simp

lemma IsCocycle2.comp {f : G × G → A} (hf : IsCocycle2 f) (F : EqHom G A B) :
    IsCocycle2 (fun p => F (f p)) := by
  rw [isCocycle2_iff_d2Fun] at hf ⊢
  rw [d2Fun_comp, hf]
  funext p
  simp

end Comp

/-! ### Continuous additive homomorphisms `G → M`

These are the `H¹` of a module with trivial action. -/

section ContAddHom

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M]

/-- The group of locally constant additive homomorphisms from the multiplicative group `G` to
the additive group `M`; this is `H¹(G,M)` for `M` with trivial action. -/
def contAddHomSubgroup (G : Type*) [Group G] [TopologicalSpace G] (M : Type*)
    [AddCommGroup M] : AddSubgroup (G → M) where
  carrier := {φ | IsLocallyConstant φ ∧ ∀ σ τ : G, φ (σ * τ) = φ σ + φ τ}
  zero_mem' := ⟨IsLocallyConstant.const 0, by intro σ τ; simp⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, hφ'⟩ ⟨hψ, hψ'⟩
    refine ⟨hφ.add hψ, ?_⟩
    intro σ τ
    simp only [Pi.add_apply, hφ' σ τ, hψ' σ τ]
    abel
  neg_mem' := by
    rintro φ ⟨hφ, hφ'⟩
    refine ⟨hφ.neg, ?_⟩
    intro σ τ
    simp only [Pi.neg_apply, hφ' σ τ]
    abel

/-- A continuous additive homomorphism `G → M`. -/
abbrev ContAddHom (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M] :
    Type _ := ↥(contAddHomSubgroup G M)

instance instCoeFunContAddHom : CoeFun (ContAddHom G M) (fun _ => G → M) :=
  ⟨fun φ => φ.1⟩

lemma ContAddHom.isLocallyConstant (φ : ContAddHom G M) : IsLocallyConstant (φ : G → M) :=
  φ.2.1

lemma ContAddHom.map_mul (φ : ContAddHom G M) (σ τ : G) : φ (σ * τ) = φ σ + φ τ :=
  φ.2.2 σ τ

@[ext] lemma ContAddHom.ext {φ ψ : ContAddHom G M} (h : ∀ σ, φ σ = ψ σ) : φ = ψ :=
  Subtype.ext (funext h)

/-- A continuous additive homomorphism is a `1`-cocycle for the trivial action. -/
lemma ContAddHom.isCocycle1 [DistribMulAction G M] (htriv : ∀ (σ : G) (m : M), σ • m = m)
    (φ : ContAddHom G M) : IsCocycle1 (φ : G → M) := by
  intro σ τ
  change (φ : G → M) (σ * τ) = (φ : G → M) σ + σ • (φ : G → M) τ
  rw [ContAddHom.map_mul φ σ τ, htriv]

end ContAddHom


/-! ### Continuous homomorphisms out of a profinite group -/

section OpenKernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type*} [Group H]

/-- A group homomorphism out of `G` whose kernel contains an open subgroup is locally constant
(hence continuous for the discrete topology on the target). -/
lemma isLocallyConstant_of_le_open_ker (φ : G →* H) (K : Subgroup G) (hK : IsOpen (K : Set G))
    (h : K ≤ φ.ker) : IsLocallyConstant (φ : G → H) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g * x) '' (K : Set G), ?_, ⟨1, K.one_mem, by simp⟩, ?_⟩
  · exact (isOpenMap_mul_left g) _ hK
  · rintro y ⟨k, hk, rfl⟩
    simp only [map_mul]
    rw [show φ k = 1 from h hk, mul_one]

end OpenKernel

/-! ### Changing the group: restriction of the action -/

section GroupChange

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [Group H] [TopologicalSpace H]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- If `M` is a discrete `G`-module and the `H`-action on `M` is the pullback of the `G`-action
along a continuous homomorphism `ψ : H →* G`, then `M` is a discrete `H`-module. -/
lemma isDiscreteGModule_of_compat [DistribMulAction H M] (ψ : H →* G) (hψ : Continuous ψ)
    (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m) [IsDiscreteGModule G M] :
    IsDiscreteGModule H M where
  isLocallyConstant_smul m := by
    have h1 : IsLocallyConstant fun h : H => ψ h • m :=
      (IsDiscreteGModule.isLocallyConstant_smul (G := G) m).comp_continuous hψ
    simpa only [hcomp] using h1

end GroupChange

end Work.ConCohomology
