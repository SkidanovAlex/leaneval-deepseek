/-
Copyright (c) 2025. All rights reserved.

# Continuous cohomology in low degrees (definitions)

This file sets up *continuous* group cohomology in degrees `0, 1, 2` for a topological group `G`
and a coefficient module `M` on which `G` acts "continuously for the discrete topology of `M`".

Since the coefficient modules of this chapter (roots of unity, units of a field, finite Galois
modules) all carry the discrete topology, and since several of them (e.g. `(k̄)ˣ`) have no
canonical `TopologicalSpace` instance in Mathlib, continuity into a discrete module is recorded
*internally* as **local constancy**:

* `Work.AbsoluteKummer.IsLocallyConstant f` — every point has an open neighbourhood on which `f`
  is constant.  For a map into a discrete space this is exactly continuity
  (`Work.AbsoluteKummer.isLocallyConstant_iff_continuous`).

The continuity of the *action* is recorded as

* `Work.AbsoluteKummer.IsDiscreteModule G M` — every `m : M` has an open stabiliser.  When `M` is
  discrete this is exactly the continuity of the map `G × M → M`, `(g, m) ↦ g • m`
  (`Work.AbsoluteKummer.isDiscreteModule_iff_continuous_smul`).

## Main definitions

* `C1c`, `C2c` — locally constant `1`- and `2`-cochains;
* `Z1`, `B1`, `Z2`, `B2` — continuous cocycles and coboundaries;
* `H0`, `H1`, `H2` — the cohomology groups `H⁰(G,M) = M^G`, `H¹ = Z¹/B¹`, `H² = Z²/B²`;
* `H1π`, `H2π` — the quotient maps.

The underlying *algebraic* cochain complex (`d0`, `d1`, `d2`, `Z1`, `B1`, `Z2`, `B2` for arbitrary
cochains) is `Submission.Work.GroupCohomology`; this file only adds the topological condition.
-/
import Mathlib
import Submission.Work.GroupCohomology.Basic
import Submission.Work.GroupCohomology.Inflation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.AbsoluteKummer

open scoped Classical Topology
open Filter

noncomputable section

/-! ## Local constancy -/

section LocallyConstant

variable {X : Type u} [TopologicalSpace X] {M : Type v}

/-- `f` is locally constant at `x`: `f` is constant on an open neighbourhood of `x`. -/
def IsLocallyConstantAt (f : X → M) (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x

/-- `f` is locally constant: it is locally constant at every point.  For a map into a discrete
space this is exactly continuity. -/
def IsLocallyConstant (f : X → M) : Prop := ∀ x : X, IsLocallyConstantAt f x

theorem isLocallyConstantAt_iff {f : X → M} {x : X} :
    IsLocallyConstantAt f x ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x := Iff.rfl

theorem isLocallyConstant_iff {f : X → M} :
    IsLocallyConstant f ↔ ∀ x : X, IsLocallyConstantAt f x := Iff.rfl

theorem isLocallyConstantAt_const (m : M) (x : X) : IsLocallyConstantAt (fun _ : X => m) x :=
  ⟨Set.univ, isOpen_univ, trivial, fun _ _ => rfl⟩

theorem isLocallyConstant_const (m : M) : IsLocallyConstant (fun _ : X => m) :=
  fun x => isLocallyConstantAt_const m x

theorem IsLocallyConstantAt.add {f g : X → M} [Add M] {x : X}
    (hf : IsLocallyConstantAt f x) (hg : IsLocallyConstantAt g x) :
    IsLocallyConstantAt (fun y => f y + g y) x := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf
  obtain ⟨V, hV, hxV, hgV⟩ := hg
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  rintro y ⟨hyU, hyV⟩
  show f y + g y = f x + g x
  rw [hfU y hyU, hgV y hyV]

theorem IsLocallyConstantAt.neg {f : X → M} [Neg M] {x : X} (hf : IsLocallyConstantAt f x) :
    IsLocallyConstantAt (fun y => -f y) x := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf
  refine ⟨U, hU, hxU, fun y hy => ?_⟩
  show -f y = -f x
  rw [hfU y hy]

theorem IsLocallyConstantAt.sub {f g : X → M} [Sub M] {x : X}
    (hf : IsLocallyConstantAt f x) (hg : IsLocallyConstantAt g x) :
    IsLocallyConstantAt (fun y => f y - g y) x := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf
  obtain ⟨V, hV, hxV, hgV⟩ := hg
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  rintro y ⟨hyU, hyV⟩
  show f y - g y = f x - g x
  rw [hfU y hyU, hgV y hyV]

theorem IsLocallyConstantAt.congr {f g : X → M} {x : X} (h : ∀ y, f y = g y)
    (hf : IsLocallyConstantAt f x) : IsLocallyConstantAt g x := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf
  exact ⟨U, hU, hxU, fun y hy => by rw [← h y, ← h x, hfU y hy]⟩

theorem IsLocallyConstant.congr {f g : X → M} (h : ∀ y, f y = g y)
    (hf : IsLocallyConstant f) : IsLocallyConstant g := fun x => (hf x).congr h

theorem IsLocallyConstant.add {f g : X → M} [Add M] (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (fun y => f y + g y) :=
  fun x => (hf x).add (hg x)

theorem IsLocallyConstant.neg {f : X → M} [Neg M] (hf : IsLocallyConstant f) :
    IsLocallyConstant (fun y => -f y) := fun x => (hf x).neg

theorem IsLocallyConstant.sub {f g : X → M} [Sub M] (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (fun y => f y - g y) :=
  fun x => (hf x).sub (hg x)

theorem IsLocallyConstant.zero [Zero M] : IsLocallyConstant (fun _ : X => (0 : M)) :=
  isLocallyConstant_const 0

/-- Composition with an arbitrary function preserves local constancy (no continuity of the outer
map is needed, since the *domain* is what shrinks). -/
theorem IsLocallyConstant.map {N : Type w} {f : X → M} (φ : M → N) (hf : IsLocallyConstant f) :
    IsLocallyConstant (fun x => φ (f x)) := by
  intro x
  obtain ⟨U, hU, hxU, hfU⟩ := hf x
  exact ⟨U, hU, hxU, fun y hy => by show φ (f y) = φ (f x); rw [hfU y hy]⟩

/-- **Local constancy is preserved by precomposition with a continuous map.** -/
theorem IsLocallyConstant.comp {Y : Type u} [TopologicalSpace Y] {f : X → M} {φ : Y → X}
    (hf : IsLocallyConstant f) (hφ : Continuous φ) : IsLocallyConstant (f ∘ φ) := by
  intro y
  obtain ⟨U, hU, hyU, hfU⟩ := hf (φ y)
  exact ⟨φ ⁻¹' U, hU.preimage hφ, hyU, fun z hz => hfU (φ z) hz⟩

/-- **Local constancy is continuity into a discrete space.** -/
theorem isLocallyConstant_iff_continuous [TopologicalSpace M] [DiscreteTopology M] (f : X → M) :
    IsLocallyConstant f ↔ Continuous f := by
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, nhds_discrete M, tendsto_pure]
    obtain ⟨U, hU, hxU, hfU⟩ := hf x
    exact Filter.mem_of_superset (hU.mem_nhds hxU) hfU
  · intro hf x
    have h : f ⁻¹' ({f x} : Set M) ∈ 𝓝 x :=
      hf.continuousAt (IsOpen.mem_nhds (isOpen_discrete _) rfl)
    obtain ⟨U, hUs, hUo, hxU⟩ := mem_nhds_iff.mp h
    exact ⟨U, hUo, hxU, fun y hy => by simpa using hUs hy⟩

end LocallyConstant

/-! ## Continuous modules -/

section DiscreteModule

variable (G : Type u) (M : Type v) [TopologicalSpace G] [Group G] [AddCommGroup M]
variable [DistribMulAction G M]

/-- **The action of `G` on `M` is continuous for the discrete topology of `M`**: every `m : M`
has an open stabiliser in `G`.  Equivalently (when `M` is discrete) the map `G × M → M`,
`(g, m) ↦ g • m`, is continuous. -/
def IsDiscreteModule : Prop := ∀ m : M, IsOpen (MulAction.stabilizer G m : Set G)

variable {G M}

theorem isDiscreteModule_iff_continuous_smul [IsTopologicalGroup G] [TopologicalSpace M]
    [DiscreteTopology M] :
    IsDiscreteModule G M ↔ Continuous fun p : G × M => p.1 • p.2 := by
  constructor
  · intro h
    rw [continuous_iff_continuousAt]
    rintro ⟨g₀, m₀⟩
    have hUopen : IsOpen {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m₀} :=
      (h m₀).preimage (continuous_const.mul continuous_id)
    have hg₀U : g₀ ∈ {g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m₀} := by
      show g₀⁻¹ * g₀ ∈ MulAction.stabilizer G m₀
      simp
    have hconst : ∀ p ∈ ({g : G | g₀⁻¹ * g ∈ MulAction.stabilizer G m₀}) ×ˢ ({m₀} : Set M),
        p.1 • p.2 = g₀ • m₀ := by
      rintro ⟨g, m⟩ ⟨hg, hm⟩
      simp only [Set.mem_singleton_iff] at hm
      rw [hm]
      have hgm : g₀⁻¹ • (g • m₀) = m₀ := by
        rw [← mul_smul]
        exact MulAction.mem_stabilizer_iff.mp hg
      calc g • m₀ = g₀ • (g₀⁻¹ • (g • m₀)) := (smul_inv_smul g₀ (g • m₀)).symm
        _ = g₀ • m₀ := by rw [hgm]
    rw [ContinuousAt, nhds_prod_eq]
    rw [nhds_discrete M, tendsto_pure]
    refine Filter.mem_of_superset
      (Filter.prod_mem_prod (hUopen.mem_nhds hg₀U)
        (Filter.mem_pure.mpr (show m₀ ∈ ({m₀} : Set M) from rfl))) ?_
    exact hconst
  · intro h m
    have h1 : IsOpen ((fun p : G × M => p.1 • p.2) ⁻¹' ({m} : Set M)) :=
      h.isOpen_preimage _ (isOpen_discrete _)
    have h4 : (MulAction.stabilizer G m : Set G) =
        (fun g : G => (g, m)) ⁻¹' ((fun p : G × M => p.1 • p.2) ⁻¹' ({m} : Set M)) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact MulAction.mem_stabilizer_iff
    rw [h4]
    exact h1.preimage (Continuous.prodMk_left m)

end DiscreteModule

/-! ## The complex of continuous cochains -/

section Cohomology

variable (G : Type u) (M : Type v) [TopologicalSpace G] [Group G] [AddCommGroup M]
variable [DistribMulAction G M]

/-- The locally constant `1`-cochains `C¹_c(G, M)`. -/
def C1c : AddSubgroup (G → M) where
  carrier := {f | IsLocallyConstant f}
  zero_mem' := isLocallyConstant_const 0
  add_mem' := fun hf hg => hf.add hg
  neg_mem' := fun hf => hf.neg

/-- The locally constant `2`-cochains `C²_c(G, M)`. -/
def C2c : AddSubgroup (G × G → M) where
  carrier := {f | IsLocallyConstant f}
  zero_mem' := isLocallyConstant_const 0
  add_mem' := fun hf hg => hf.add hg
  neg_mem' := fun hf => hf.neg

/-- The continuous `1`-cocycles `Z¹_c(G, M)`: additive crossed homomorphisms which are locally
constant. -/
def Z1 : AddSubgroup (G → M) := Work.GroupCohomology.Z1 G M ⊓ C1c G M

/-- The continuous `1`-coboundaries `B¹_c(G, M) = im d⁰`. -/
def B1 : AddSubgroup (G → M) := (Work.GroupCohomology.d0 G M).range

/-- The continuous `2`-cocycles `Z²_c(G, M)`. -/
def Z2 : AddSubgroup (G × G → M) := Work.GroupCohomology.Z2 G M ⊓ C2c G M

/-- The continuous `2`-coboundaries `B²_c(G, M) = d¹(C¹_c(G, M))`. -/
def B2 : AddSubgroup (G × G → M) :=
  AddSubgroup.map (Work.GroupCohomology.d1 G M) (C1c G M)

/-- The `0`-th cohomology `H⁰(G,M) = M^G`, the invariants. -/
abbrev H0 : AddSubgroup M := Work.GroupCohomology.invariants G M

/-- The first continuous cohomology `H¹(G,M) = Z¹_c/B¹_c`. -/
abbrev H1 : Type (max u v) :=
  (Z1 G M : AddSubgroup (G → M)) ⧸ ((B1 G M).comap (Z1 G M).subtype)

/-- The second continuous cohomology `H²(G,M) = Z²_c/B²_c`. -/
abbrev H2 : Type (max u v) :=
  (Z2 G M : AddSubgroup (G × G → M)) ⧸ ((B2 G M).comap (Z2 G M).subtype)

/-- The quotient map `Z¹_c(G,M) → H¹(G,M)`. -/
noncomputable def H1π : (Z1 G M) →+ H1 G M :=
  QuotientAddGroup.mk' ((B1 G M).comap (Z1 G M).subtype)

/-- The quotient map `Z²_c(G,M) → H²(G,M)`. -/
noncomputable def H2π : (Z2 G M) →+ H2 G M :=
  QuotientAddGroup.mk' ((B2 G M).comap (Z2 G M).subtype)

variable {G M}

@[simp] theorem mem_C1c_iff (f : G → M) : f ∈ C1c G M ↔ IsLocallyConstant f := Iff.rfl

@[simp] theorem mem_C2c_iff (f : G × G → M) : f ∈ C2c G M ↔ IsLocallyConstant f := Iff.rfl

@[simp] theorem mem_Z1_iff (f : G → M) :
    f ∈ Z1 G M ↔ Work.GroupCohomology.IsCrossedHom G M f ∧ IsLocallyConstant f := by
  rw [Z1, AddSubgroup.mem_inf, Work.GroupCohomology.mem_Z1_iff]
  exact Iff.rfl

theorem mem_Z2_iff (c : G × G → M) :
    c ∈ Z2 G M ↔
      (∀ g h k : G, c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k)) ∧
        IsLocallyConstant c := by
  rw [Z2, AddSubgroup.mem_inf, Work.GroupCohomology.mem_Z2_iff]
  exact Iff.rfl

@[simp] theorem mem_B1_iff (f : G → M) :
    f ∈ B1 G M ↔ ∃ a : M, Work.GroupCohomology.d0 G M a = f := Iff.rfl

@[simp] theorem mem_B2_iff (c : G × G → M) :
    c ∈ B2 G M ↔ ∃ f ∈ C1c G M, Work.GroupCohomology.d1 G M f = c := Iff.rfl

theorem H1π_eq_zero_iff (f : Z1 G M) : H1π G M f = 0 ↔ (f : G → M) ∈ B1 G M := by
  rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  rfl

theorem H1π_eq_iff (f f' : Z1 G M) :
    H1π G M f = H1π G M f' ↔ ((f - f' : Z1 G M) : G → M) ∈ B1 G M := by
  rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem]
  exact Iff.rfl

theorem H2π_eq_iff (c c' : Z2 G M) :
    H2π G M c = H2π G M c' ↔ ((c - c' : Z2 G M) : G × G → M) ∈ B2 G M := by
  rw [H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap]
  rfl

theorem H2π_eq_zero_iff (c : Z2 G M) :
    H2π G M c = 0 ↔ (c : G × G → M) ∈ B2 G M := by
  rw [H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  rfl

end Cohomology

end

end Work.AbsoluteKummer
