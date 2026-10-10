import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Group.Uniform
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.Tate

open scoped BigOperators

/-! ## Fixed points -/

/-- The subgroup `A^G` of `G`-fixed points of a module `A` over the group `G`. -/
def fixedSubgroup (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] : AddSubgroup A where
  carrier := {a : A | ∀ g : G, g • a = a}
  zero_mem' := by intro g; simp
  add_mem' := by intro a b ha hb g; rw [smul_add, ha g, hb g]
  neg_mem' := by intro a ha g; rw [smul_neg, ha g]

@[simp] theorem mem_fixedSubgroup {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] {a : A} :
    a ∈ fixedSubgroup G A ↔ ∀ g : G, g • a = a := Iff.rfl

theorem smul_eq_self_of_mem_fixedSubgroup {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] {a : A} (ha : a ∈ fixedSubgroup G A) (g : G) : g • a = a := ha g

/-- The `G`-action bundled as an additive endomorphism `a ↦ g • a`. -/
def smulAddHom (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A]
    (g : G) : A →+ A where
  toFun a := g • a
  map_zero' := smul_zero g
  map_add' a b := smul_add g a b

@[simp] theorem smulAddHom_apply {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (g : G) (a : A) : smulAddHom G A g a = g • a := rfl

/-- Scalar multiplication distributes over a finite sum. -/
theorem smul_sum_finset {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (g : G) (s : Finset G) (F : G → A) :
    g • (∑ h ∈ s, F h) = ∑ h ∈ s, g • F h := by
  classical
  exact Finset.induction_on s
    (show g • (∑ h ∈ (∅ : Finset G), F h) = ∑ h ∈ (∅ : Finset G), g • F h by simp)
    (fun a t hat ih => by
      show g • (∑ h ∈ insert a t, F h) = ∑ h ∈ insert a t, g • F h
      rw [Finset.sum_insert hat, Finset.sum_insert hat, smul_add, ih])

/-- Scalar multiplication distributes over the sum over a finite type. -/
theorem smul_sum_univ {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (g : G) (F : G → A) :
    g • (∑ h : G, F h) = ∑ h : G, g • F h :=
  smul_sum_finset g Finset.univ F

/-- Addition distributes over the sum over a finite type. -/
theorem sum_add_distrib_univ {ι : Type u} {M : Type v} [AddCommMonoid M] [Fintype ι]
    (f g : ι → M) : (∑ x : ι, (f x + g x)) = (∑ x : ι, f x) + ∑ x : ι, g x := by
  classical
  exact Finset.induction_on (Finset.univ : Finset ι)
    (show (∑ x ∈ (∅ : Finset ι), (f x + g x))
        = (∑ x ∈ (∅ : Finset ι), f x) + ∑ x ∈ (∅ : Finset ι), g x by simp)
    (fun a t hat ih => by
      show (∑ x ∈ insert a t, (f x + g x))
          = (∑ x ∈ insert a t, f x) + ∑ x ∈ insert a t, g x
      rw [Finset.sum_insert hat, Finset.sum_insert hat, Finset.sum_insert hat, ih]
      ac_rfl)

/-- An additive homomorphism commutes with the sum over a finite type. -/
theorem map_sum_univ {G : Type u} {M : Type v} {N : Type w} [AddCommMonoid M]
    [AddCommMonoid N] [Fintype G] (f : M →+ N) (F : G → M) :
    f (∑ g : G, F g) = ∑ g : G, f (F g) := by
  classical
  exact Finset.induction_on (Finset.univ : Finset G)
    (show f (∑ g ∈ (∅ : Finset G), F g) = ∑ g ∈ (∅ : Finset G), f (F g) by simp)
    (fun a t hat ih => by
      show f (∑ g ∈ insert a t, F g) = ∑ g ∈ insert a t, f (F g)
      rw [Finset.sum_insert hat, Finset.sum_insert hat, map_add, ih])

/-- Passing to a product of indices preserves finite sums. -/
theorem sum_mulLeft_invariant {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (F : G → A) (g : G) :
    (∑ h : G, F (g * h)) = ∑ h : G, F h :=
  Fintype.sum_equiv (Equiv.mulLeft g) (fun h => F (g * h)) (fun k => F k) (fun _ => rfl)

theorem sum_mulRight_invariant {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (F : G → A) (g : G) :
    (∑ h : G, F (h * g)) = ∑ h : G, F h :=
  Fintype.sum_equiv (Equiv.mulRight g) (fun h => F (h * g)) (fun k => F k) (fun _ => rfl)

/-! ## The norm -/

/-- The norm endomorphism `N a = ∑_{g : G} g • a` of a module over a finite group. -/
noncomputable def norm (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : A →+ A where
  toFun a := ∑ g : G, g • a
  map_zero' := by simp
  map_add' a b := by
    show (∑ g : G, g • (a + b)) = (∑ g : G, g • a) + ∑ g : G, g • b
    rw [Finset.sum_congr rfl (fun g _ => smul_add g a b)]
    exact sum_add_distrib_univ (fun g => g • a) (fun g => g • b)

@[simp] theorem norm_apply {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (a : A) : norm G A a = ∑ g : G, g • a := rfl

/-- The norm is invariant under the action: `N (g • a) = N a`. -/
theorem norm_smul {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (g : G) (a : A) : norm G A (g • a) = norm G A a := by
  have h1 : norm G A (g • a) = ∑ h : G, (h * g) • a := by
    rw [norm_apply]
    exact Finset.sum_congr rfl (fun h _ => by rw [mul_smul])
  rw [h1, norm_apply]
  exact sum_mulRight_invariant (fun k => k • a) g

/-- The norm takes values in the fixed points. -/
theorem norm_mem_fixed {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (a : A) : norm G A a ∈ fixedSubgroup G A := by
  rw [mem_fixedSubgroup]
  intro g
  have h2 : g • (∑ h : G, h • a) = ∑ h : G, (g * h) • a := by
    rw [smul_sum_univ]
    exact Finset.sum_congr rfl (fun h _ => by rw [mul_smul])
  rw [norm_apply a, h2]
  exact sum_mulLeft_invariant (fun k => k • a) g

/-- For a fixed point `a`, `g • a = a`, so `g • N a = N a`. -/
theorem smul_norm {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (g : G) (a : A) : g • norm G A a = norm G A (g • a) := by
  rw [(norm_mem_fixed a) g, norm_smul]

/-- The norm commutes with `G`-equivariant additive maps. -/
theorem norm_map {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : A) :
    norm G B (f a) = f (norm G A a) := by
  have hB : norm G B (f a) = ∑ g : G, g • f a := rfl
  have hA : f (norm G A a) = ∑ g : G, f (g • a) := by
    rw [norm_apply, map_sum_univ f (fun g => g • a)]
  rw [hB, hA]
  exact Finset.sum_congr rfl (fun g _ => (hf g a).symm)

/-! ## The augmentation submodule -/

/-- The augmentation submodule `I_G · A` of a `G`-module `A`: the additive subgroup generated
by the elements `g • a - a`.  Equivalently the image of the augmentation ideal of `ℤ[G]`. -/
def augmentation (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] : AddSubgroup A :=
  AddSubgroup.closure (Set.range fun p : G × A => p.1 • p.2 - p.2)

theorem smul_sub_self_mem_augmentation {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (g : G) (a : A) : g • a - a ∈ augmentation G A :=
  AddSubgroup.subset_closure ⟨(g, a), rfl⟩

theorem zero_mem_augmentation {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] : (0 : A) ∈ augmentation G A :=
  AddSubgroup.zero_mem _

/-- The augmentation submodule is contained in the kernel of the norm. -/
theorem augmentation_le_ker_norm {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : augmentation G A ≤ (norm G A).ker := by
  rw [augmentation, AddSubgroup.closure_le]
  rintro _ ⟨⟨g, a⟩, rfl⟩
  show norm G A (g • a - a) = 0
  rw [map_sub, norm_smul, sub_self]

/-- Elements of the augmentation submodule are killed by the norm. -/
theorem norm_eq_zero_of_mem_augmentation {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] {a : A} (ha : a ∈ augmentation G A) : norm G A a = 0 :=
  AddMonoidHom.mem_ker.mp (augmentation_le_ker_norm ha)

/-- A `G`-equivariant additive map sends the augmentation submodule into the augmentation
submodule. -/
theorem map_le_augmentation {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    (augmentation G A).map f ≤ augmentation G B := by
  rw [AddSubgroup.map_le_iff_le_comap, augmentation, AddSubgroup.closure_le]
  rintro _ ⟨⟨g, a⟩, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap, map_sub, hf g a]
  exact smul_sub_self_mem_augmentation g (f a)

/-- Elements of the augmentation submodule map into the augmentation submodule. -/
theorem map_mem_augmentation {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) {a : A}
    (ha : a ∈ augmentation G A) : f a ∈ augmentation G B :=
  map_le_augmentation f hf (AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩)

/-! ## The two Tate groups -/

/-- The norm, regarded as a map `A → A^G`. -/
noncomputable def normToFixed (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : A →+ fixedSubgroup G A where
  toFun a := ⟨norm G A a, norm_mem_fixed a⟩
  map_zero' := Subtype.ext (map_zero (norm G A))
  map_add' a b := Subtype.ext (map_add (norm G A) a b)

@[simp] theorem normToFixed_apply {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (a : A) :
    (normToFixed G A a : A) = norm G A a := rfl

/-- `Ĥ⁰(G, A) = A^G / N(A)`. -/
noncomputable abbrev H0 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] := (fixedSubgroup G A) ⧸ (normToFixed G A).range

/-- The quotient map `A^G → Ĥ⁰(G, A)`. -/
noncomputable def H0π (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : fixedSubgroup G A →+ H0 G A :=
  QuotientAddGroup.mk' _

/-- The image of the augmentation submodule inside the kernel of the norm. -/
noncomputable abbrev augInKer (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : AddSubgroup (norm G A).ker :=
  (augmentation G A).comap (norm G A).ker.subtype

/-- `Ĥ⁻¹(G, A) = ker N / I_G·A`. -/
noncomputable abbrev Hm1 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] := (norm G A).ker ⧸ augInKer G A

/-- The quotient map `ker N → Ĥ⁻¹(G, A)`. -/
noncomputable def Hm1π (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : (norm G A).ker →+ Hm1 G A :=
  QuotientAddGroup.mk' _

/-! ## API for the quotient groups -/

theorem H0π_eq_zero_iff {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (x : fixedSubgroup G A) :
    H0π G A x = 0 ↔ x ∈ (normToFixed G A).range :=
  QuotientAddGroup.eq_zero_iff x

theorem H0π_eq_iff {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (x y : fixedSubgroup G A) :
    H0π G A x = H0π G A y ↔ x - y ∈ (normToFixed G A).range :=
  QuotientAddGroup.eq_iff_sub_mem

theorem H0π_surjective {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : Function.Surjective (H0π G A) :=
  QuotientAddGroup.mk'_surjective _

theorem H0_induction_on {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] {C : H0 G A → Prop} (x : H0 G A)
    (h : ∀ a : fixedSubgroup G A, C (H0π G A a)) : C x := by
  obtain ⟨a, rfl⟩ := H0π_surjective x
  exact h a

theorem Hm1π_eq_zero_iff {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (x : (norm G A).ker) :
    Hm1π G A x = 0 ↔ (x : A) ∈ augmentation G A :=
  QuotientAddGroup.eq_zero_iff x

theorem Hm1π_eq_iff {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (x y : (norm G A).ker) :
    Hm1π G A x = Hm1π G A y ↔ (x - y : (norm G A).ker) ∈ augInKer G A :=
  QuotientAddGroup.eq_iff_sub_mem

theorem Hm1π_surjective {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : Function.Surjective (Hm1π G A) :=
  QuotientAddGroup.mk'_surjective _

theorem Hm1_induction_on {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] {C : Hm1 G A → Prop} (x : Hm1 G A)
    (h : ∀ a : (norm G A).ker, C (Hm1π G A a)) : C x := by
  obtain ⟨a, rfl⟩ := Hm1π_surjective x
  exact h a

/-- Two elements of the kernel of the norm have the same class in `Ĥ⁻¹(G, A)` as soon as they
differ by an element of the augmentation submodule. -/
theorem Hm1π_eq_of_sub_mem {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] (x y : (norm G A).ker)
    (h : (x - y : (norm G A).ker) ∈ augInKer G A) : Hm1π G A x = Hm1π G A y :=
  (Hm1π_eq_iff x y).mpr h

/-! ## Functoriality -/

/-- A `G`-equivariant additive map restricts to the fixed points. -/
noncomputable def mapFixed (G : Type u) (A : Type v) (B : Type w) [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    fixedSubgroup G A →+ fixedSubgroup G B where
  toFun a := ⟨f a, by
    rw [mem_fixedSubgroup]
    intro g
    rw [← hf g (a : A), a.2 g]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : A) (b : A))

@[simp] theorem mapFixed_apply {G : Type u} {A : Type v} {B : Type w} [Group G]
    [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : fixedSubgroup G A) :
    (mapFixed G A B f hf a : B) = f a := rfl

/-- A `G`-equivariant additive map restricts to the kernels of the norms. -/
noncomputable def mapKer (G : Type u) (A : Type v) (B : Type w) [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    (norm G A).ker →+ (norm G B).ker where
  toFun a := ⟨f a, by
    rw [AddMonoidHom.mem_ker, norm_map f hf (a : A), a.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : A) (b : A))

@[simp] theorem mapKer_apply {G : Type u} {A : Type v} {B : Type w} [Group G]
    [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : (norm G A).ker) :
    (mapKer G A B f hf a : B) = f a := rfl

/-- The induced map `Ĥ⁰(G, A) → Ĥ⁰(G, B)`. -/
noncomputable def H0Map (G : Type u) (A : Type v) (B : Type w) [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    H0 G A →+ H0 G B :=
  QuotientAddGroup.map _ _ (mapFixed G A B f hf) (by
    rintro _ ⟨a, rfl⟩
    rw [AddSubgroup.mem_comap]
    exact ⟨f a, Subtype.ext (norm_map f hf a)⟩)

/-- The induced map `Ĥ⁻¹(G, A) → Ĥ⁻¹(G, B)`. -/
noncomputable def Hm1Map (G : Type u) (A : Type v) (B : Type w) [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Hm1 G A →+ Hm1 G B :=
  QuotientAddGroup.map _ _ (mapKer G A B f hf) (by
    intro x hx
    rw [AddSubgroup.mem_comap] at hx ⊢
    exact map_mem_augmentation f hf hx)

@[simp] theorem H0Map_H0π {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : fixedSubgroup G A) :
    H0Map G A B f hf (H0π G A a) = H0π G B (mapFixed G A B f hf a) := rfl

@[simp] theorem Hm1Map_Hm1π {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B] [Fintype G]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : (norm G A).ker) :
    Hm1Map G A B f hf (Hm1π G A a) = Hm1π G B (mapKer G A B f hf a) := rfl

end Work.Tate
