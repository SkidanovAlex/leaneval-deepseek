/-
Copyright: the martinet_totally_real_towers team.

# Continuous cohomology of a topological group with discrete coefficients

This is the base module of the chapter `Work.ConCohomology`.  It sets up the *inhomogeneous*
cochain complex of a topological group `G` acting continuously on a discrete abelian group `M`,
together with its low degree cohomology `H⁰`, `H¹`, `H²`.

## Conventions

* `G` is a group with a topology making it a topological group; in the intended applications
  `G` is a profinite group (a Galois group with the Krull topology).
* `M` carries a `DistribMulAction G M` structure (written additively) and the class
  `IsDiscreteGModule G M` says that the stabilizer of every point is open -- equivalently that
  the action map `G × M → M` is continuous when `M` is given the discrete topology.  We record
  the equivalent statement `∀ m, IsLocallyConstant (fun g : G => g • m)`.
* Cochains are *locally constant* functions (`LocallyConstant`); as `M` is to be thought of as
  discrete, this is exactly continuity.  No topology on `M` itself is needed.
* `d⁰, d¹, d²` are the inhomogeneous differentials, given on plain functions by
  `d⁰m (σ) = σ•m - m`,
  `d¹f (σ,τ) = σ•f τ - f(στ) + f σ`,
  `d²f (σ,τ,ρ) = σ•f(τ,ρ) - f(στ,ρ) + f(σ,τρ) - f(σ,τ)`.
  So `Z¹` is the group of (continuous) crossed homomorphisms `G → M` and `Z²` the group of
  (continuous) factor systems.

## Main definitions

* `Work.ConCohomology.IsDiscreteGModule`
* `Work.ConCohomology.Cochain1`, `Cochain2`, `Cochain3`
* `Work.ConCohomology.d0Fun`, `d1Fun`, `d2Fun`, `d0Hom`, `d1Hom`, `d2Hom`
* `Work.ConCohomology.Z1`, `B1`, `Z2`, `B2`, `H0`, `H1`, `H2`

-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function

universe u

section Basic

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- A discrete `G`-module: the action of `G` on `M` is continuous for the discrete topology on
`M`, equivalently the stabilizer of every point of `M` is open in `G`.  We record the equivalent
local-constancy form, which is the form actually used. -/
class IsDiscreteGModule (G : Type*) [Group G] [TopologicalSpace G] (M : Type*)
    [AddCommGroup M] [DistribMulAction G M] : Prop where
  isLocallyConstant_smul : ∀ m : M, IsLocallyConstant fun g : G => g • m

instance instIsDiscreteGModuleSubsingleton [Subsingleton M] : IsDiscreteGModule G M where
  isLocallyConstant_smul m := IsLocallyConstant.of_constant _ fun _ _ => Subsingleton.elim _ _

/-- The stabilizer of a point of a discrete module is open. -/
lemma isOpen_stabilizer [IsDiscreteGModule G M] (m : M) :
    IsOpen {g : G | g • m = m} :=
  (IsDiscreteGModule.isLocallyConstant_smul (G := G) m).isOpen_fiber m

/-! ### The inhomogeneous differentials, as operations on plain functions -/

/-- The zeroth inhomogeneous coboundary. -/
def d0Fun (m : M) : G → M := fun σ => σ • m - m

/-- The first inhomogeneous coboundary. -/
def d1Fun (f : G → M) : G × G → M := fun p => p.1 • f p.2 - f (p.1 * p.2) + f p.1

/-- The second inhomogeneous coboundary. -/
def d2Fun (f : G × G → M) : G × G × G → M :=
  fun p => p.1 • f (p.2.1, p.2.2) - f (p.1 * p.2.1, p.2.2) + f (p.1, p.2.1 * p.2.2)
    - f (p.1, p.2.1)

@[simp] lemma d0Fun_apply (m : M) (σ : G) : d0Fun (G := G) m σ = σ • m - m := rfl

@[simp] lemma d1Fun_apply (f : G → M) (σ τ : G) :
    d1Fun f (σ, τ) = σ • f τ - f (σ * τ) + f σ := rfl

@[simp] lemma d2Fun_apply (f : G × G → M) (σ τ ρ : G) :
    d2Fun f (σ, τ, ρ) = σ • f (τ, ρ) - f (σ * τ, ρ) + f (σ, τ * ρ) - f (σ, τ) := rfl

lemma d1Fun_d0Fun (m : M) : d1Fun (d0Fun (G := G) m) = 0 := by
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Fun_apply, d0Fun_apply, Pi.zero_apply]
  rw [smul_sub, mul_smul]
  abel

lemma d2Fun_d1Fun (f : G → M) : d2Fun (d1Fun f) = 0 := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply, d1Fun_apply, Pi.zero_apply]
  rw [smul_add, smul_sub, mul_smul, mul_assoc]
  abel

/-- `d¹` is additive in its argument. -/
lemma d1Fun_add (f g : G → M) : d1Fun (f + g) = d1Fun f + d1Fun g := by
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Fun_apply, Pi.add_apply]
  rw [smul_add]
  abel

/-- `d²` is additive in its argument. -/
lemma d2Fun_add (f g : G × G → M) : d2Fun (f + g) = d2Fun f + d2Fun g := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply, Pi.add_apply]
  rw [smul_add]
  abel

lemma d1Fun_neg (f : G → M) : d1Fun (-f) = -d1Fun f := by
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Fun_apply, Pi.neg_apply]
  rw [smul_neg]
  abel

lemma d2Fun_neg (f : G × G → M) : d2Fun (-f) = -d2Fun f := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply, Pi.neg_apply]
  rw [smul_neg]
  abel

/-! ### The cocycle conditions -/

/-- A `1`-cocycle: a continuous crossed homomorphism `G → M`. -/
def IsCocycle1 (f : G → M) : Prop := ∀ σ τ, f (σ * τ) = f σ + σ • f τ

/-- A `2`-cocycle: a continuous factor system. -/
def IsCocycle2 (f : G × G → M) : Prop :=
  ∀ σ τ ρ, σ • f (τ, ρ) - f (σ * τ, ρ) + f (σ, τ * ρ) - f (σ, τ) = 0

lemma isCocycle1_iff_d1Fun (f : G → M) : IsCocycle1 f ↔ d1Fun f = 0 := by
  constructor
  · intro h
    funext p
    obtain ⟨σ, τ⟩ := p
    simp only [d1Fun_apply, Pi.zero_apply]
    rw [h σ τ]
    abel
  · intro h σ τ
    have h2 : σ • f τ - f (σ * τ) + f σ = 0 := by
      have := congrFun h (σ, τ)
      simpa [d1Fun] using this
    have h3 : f (σ * τ) = σ • f τ + f σ := by
      rw [eq_comm, ← sub_eq_zero]
      abel_nf at h2 ⊢
      exact h2
    rw [h3]
    abel

lemma isCocycle2_iff_d2Fun (f : G × G → M) : IsCocycle2 f ↔ d2Fun f = 0 := by
  constructor
  · intro h
    funext p
    obtain ⟨σ, τ, ρ⟩ := p
    simpa using h σ τ ρ
  · intro h σ τ ρ
    have := congrFun h (σ, τ, ρ)
    simpa using this

lemma isCocycle1_zero : IsCocycle1 (G := G) (M := M) (fun _ => 0) := by
  intro σ τ
  simp

lemma isCocycle2_zero : IsCocycle2 (G := G) (M := M) (fun _ => 0) := by
  intro σ τ ρ
  simp

lemma isCocycle1_add {f g : G → M} (hf : IsCocycle1 f) (hg : IsCocycle1 g) :
    IsCocycle1 (f + g) := by
  rw [isCocycle1_iff_d1Fun] at hf hg ⊢
  rw [d1Fun_add, hf, hg, add_zero]

lemma isCocycle2_add {f g : G × G → M} (hf : IsCocycle2 f) (hg : IsCocycle2 g) :
    IsCocycle2 (f + g) := by
  rw [isCocycle2_iff_d2Fun] at hf hg ⊢
  rw [d2Fun_add, hf, hg, add_zero]

lemma isCocycle1_neg {f : G → M} (hf : IsCocycle1 f) : IsCocycle1 (-f) := by
  rw [isCocycle1_iff_d1Fun] at hf ⊢
  rw [d1Fun_neg, hf, neg_zero]

lemma isCocycle2_neg {f : G × G → M} (hf : IsCocycle2 f) : IsCocycle2 (-f) := by
  rw [isCocycle2_iff_d2Fun] at hf ⊢
  rw [d2Fun_neg, hf, neg_zero]

lemma isCocycle1_sub {f g : G → M} (hf : IsCocycle1 f) (hg : IsCocycle1 g) :
    IsCocycle1 (f - g) := by
  rw [sub_eq_add_neg]
  exact isCocycle1_add hf (isCocycle1_neg hg)

lemma isCocycle2_sub {f g : G × G → M} (hf : IsCocycle2 f) (hg : IsCocycle2 g) :
    IsCocycle2 (f - g) := by
  rw [sub_eq_add_neg]
  exact isCocycle2_add hf (isCocycle2_neg hg)

end Basic

/-! ### The locally constant cochains and the bundled differentials -/

/-- The group of `1`-cochains: locally constant functions `G → M`. -/
abbrev Cochain1 (G : Type*) [TopologicalSpace G] (M : Type*) := LocallyConstant G M

/-- The group of `2`-cochains: locally constant functions `G × G → M`. -/
abbrev Cochain2 (G : Type*) [TopologicalSpace G] (M : Type*) := LocallyConstant (G × G) M

/-- The group of `3`-cochains: locally constant functions `G × G × G → M`.  This is only used to
define `Z²` as a kernel; no cohomology is taken in degree `3`. -/
abbrev Cochain3 (G : Type*) [TopologicalSpace G] (M : Type*) :=
  LocallyConstant (G × G × G) M

section LocallyConstantLemmas

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]

/-- The pointwise product of a continuous `G`-valued function and a locally constant `M`-valued
function is locally constant. -/
lemma isLocallyConstant_smul_comp {X : Type*} [TopologicalSpace X] {φ : X → M} {s : X → G}
    (hφ : IsLocallyConstant φ) (hs : Continuous s) :
    IsLocallyConstant fun x => s x • φ x := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨V, hV, hxV, hVc⟩ :=
    (IsDiscreteGModule.isLocallyConstant_smul (G := G) (φ x)).exists_open (s x)
  obtain ⟨U, hU, hxU, hUc⟩ := hφ.exists_open x
  refine ⟨s ⁻¹' V ∩ U, (hs.isOpen_preimage V hV).inter hU, ⟨hxV, hxU⟩, ?_⟩
  rintro y ⟨hyV, hyU⟩
  rw [hUc y hyU, hVc (s y) hyV]

lemma isLocallyConstant_d0Fun (m : M) : IsLocallyConstant (d0Fun (G := G) m) :=
  (IsDiscreteGModule.isLocallyConstant_smul (G := G) m).sub (IsLocallyConstant.const _)

@[simp] lemma diff1_apply (f : Cochain1 G M) (σ τ : G) :
    d1Fun (f : G → M) (σ, τ) = σ • f τ - f (σ * τ) + f σ := rfl

@[simp] lemma diff2_apply (f : Cochain2 G M) (σ τ ρ : G) :
    d2Fun (f : G × G → M) (σ, τ, ρ) =
      σ • f (τ, ρ) - f (σ * τ, ρ) + f (σ, τ * ρ) - f (σ, τ) := rfl

lemma isLocallyConstant_d1Fun (f : Cochain1 G M) : IsLocallyConstant (d1Fun (f : G → M)) := by
  have h1 : IsLocallyConstant fun p : G × G => p.1 • f p.2 :=
    isLocallyConstant_smul_comp (φ := fun p : G × G => f p.2)
      (f.isLocallyConstant.comp_continuous continuous_snd) continuous_fst
  have h2 : IsLocallyConstant fun p : G × G => f (p.1 * p.2) :=
    f.isLocallyConstant.comp_continuous (continuous_fst.mul continuous_snd)
  have h3 : IsLocallyConstant fun p : G × G => f p.1 :=
    f.isLocallyConstant.comp_continuous continuous_fst
  exact (h1.sub h2).add h3

lemma isLocallyConstant_d2Fun (f : Cochain2 G M) :
    IsLocallyConstant (d2Fun (f : G × G → M)) := by
  have hφ : IsLocallyConstant fun p : G × G × G => f (p.2.1, p.2.2) :=
    f.isLocallyConstant.comp_continuous
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd))
  have h1 : IsLocallyConstant fun p : G × G × G => p.1 • f (p.2.1, p.2.2) :=
    isLocallyConstant_smul_comp (φ := fun p : G × G × G => f (p.2.1, p.2.2)) hφ continuous_fst
  have h2 : IsLocallyConstant fun p : G × G × G => f (p.1 * p.2.1, p.2.2) :=
    f.isLocallyConstant.comp_continuous
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))
  have h3 : IsLocallyConstant fun p : G × G × G => f (p.1, p.2.1 * p.2.2) :=
    f.isLocallyConstant.comp_continuous
      (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).mul
        (continuous_snd.comp continuous_snd)))
  have h4 : IsLocallyConstant fun p : G × G × G => f (p.1, p.2.1) :=
    f.isLocallyConstant.comp_continuous
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  exact ((h1.sub h2).add h3).sub h4

/-- The zeroth differential as a homomorphism `M → C¹(G,M)`. -/
def d0Hom (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    M →+ Cochain1 G M where
  toFun m := ⟨d0Fun m, isLocallyConstant_d0Fun m⟩
  map_zero' := by
    ext σ
    show d0Fun (G := G) (M := M) 0 σ = (0 : G → M) σ
    simp [d0Fun]
  map_add' m n := by
    ext σ
    show d0Fun (G := G) (M := M) (m + n) σ =
      d0Fun (G := G) (M := M) m σ + d0Fun (G := G) (M := M) n σ
    simp only [d0Fun_apply, smul_add]
    abel

/-- The first differential as a homomorphism `C¹(G,M) → C²(G,M)`. -/
def d1Hom (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    Cochain1 G M →+ Cochain2 G M where
  toFun f := ⟨d1Fun (f : G → M), isLocallyConstant_d1Fun f⟩
  map_zero' := by
    ext p
    obtain ⟨σ, τ⟩ := p
    show d1Fun (G := G) (M := M) (0 : G → M) (σ, τ) = (0 : G × G → M) (σ, τ)
    simp [d1Fun]
  map_add' f g := by
    ext p
    obtain ⟨σ, τ⟩ := p
    show d1Fun (f + g : G → M) (σ, τ) = (d1Fun (f : G → M) + d1Fun (g : G → M)) (σ, τ)
    simp only [d1Fun_apply, Pi.add_apply, smul_add]
    abel

/-- The second differential as a homomorphism `C²(G,M) → C³(G,M)`. -/
def d2Hom (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    Cochain2 G M →+ Cochain3 G M where
  toFun f := ⟨d2Fun (f : G × G → M), isLocallyConstant_d2Fun f⟩
  map_zero' := by
    ext p
    obtain ⟨σ, τ, ρ⟩ := p
    show d2Fun (G := G) (M := M) (0 : G × G → M) (σ, τ, ρ) =
      (0 : G × G × G → M) (σ, τ, ρ)
    simp [d2Fun]
  map_add' f g := by
    ext p
    obtain ⟨σ, τ, ρ⟩ := p
    show d2Fun (f + g : G × G → M) (σ, τ, ρ) =
      (d2Fun (f : G × G → M) + d2Fun (g : G × G → M)) (σ, τ, ρ)
    simp only [d2Fun_apply, Pi.add_apply, smul_add]
    abel

@[simp] lemma d0Hom_apply (m : M) (σ : G) : d0Hom G M m σ = σ • m - m := rfl

@[simp] lemma d1Hom_apply (f : Cochain1 G M) (σ τ : G) :
    d1Hom G M f (σ, τ) = σ • f τ - f (σ * τ) + f σ := rfl

@[simp] lemma d2Hom_apply (f : Cochain2 G M) (σ τ ρ : G) :
    d2Hom G M f (σ, τ, ρ) = σ • f (τ, ρ) - f (σ * τ, ρ) + f (σ, τ * ρ) - f (σ, τ) := rfl

lemma d1Hom_comp_d0Hom : (d1Hom G M).comp (d0Hom G M) = 0 := by
  ext m p
  obtain ⟨σ, τ⟩ := p
  simpa using congrFun (d1Fun_d0Fun (G := G) m) (σ, τ)

lemma d2Hom_comp_d1Hom : (d2Hom G M).comp (d1Hom G M) = 0 := by
  ext f p
  obtain ⟨σ, τ, ρ⟩ := p
  simpa using congrFun (d2Fun_d1Fun (f : G → M)) (σ, τ, ρ)

end LocallyConstantLemmas

/-! ### Cocycles, coboundaries and the low degree cohomology groups -/

section Cohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]

/-- The group of `1`-cocycles: continuous crossed homomorphisms `G → M`. -/
def Z1 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Cochain1 G M) := (d1Hom G M).ker

/-- The group of `1`-coboundaries. -/
def B1 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Cochain1 G M) := (d0Hom G M).range

/-- The group of `2`-cocycles. -/
def Z2 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Cochain2 G M) := (d2Hom G M).ker

/-- The group of `2`-coboundaries. -/
def B2 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Cochain2 G M) := (d1Hom G M).range

lemma d1Hom_eq_zero_iff (f : Cochain1 G M) : d1Hom G M f = 0 ↔ d1Fun (f : G → M) = 0 := by
  constructor
  · intro h
    have h' : d1Fun (f : G → M) = 0 := by
      have := congrArg (fun g : Cochain2 G M => (g : G × G → M)) h
      simpa [d1Hom] using this
    exact h'
  · intro h
    ext p
    simp [d1Hom, h]

lemma d2Hom_eq_zero_iff (f : Cochain2 G M) : d2Hom G M f = 0 ↔ d2Fun (f : G × G → M) = 0 := by
  constructor
  · intro h
    have h' : d2Fun (f : G × G → M) = 0 := by
      have := congrArg (fun g : Cochain3 G M => (g : G × G × G → M)) h
      simpa [d2Hom] using this
    exact h'
  · intro h
    ext p
    simp [d2Hom, h]

@[simp] lemma mem_Z1 {f : Cochain1 G M} : f ∈ Z1 G M ↔ IsCocycle1 (f : G → M) := by
  rw [Z1, AddMonoidHom.mem_ker, d1Hom_eq_zero_iff, ← isCocycle1_iff_d1Fun]

@[simp] lemma mem_B1 {f : Cochain1 G M} : f ∈ B1 G M ↔ ∃ m : M, d0Hom G M m = f :=
  AddMonoidHom.mem_range

@[simp] lemma mem_Z2 {f : Cochain2 G M} : f ∈ Z2 G M ↔ IsCocycle2 (f : G × G → M) := by
  rw [Z2, AddMonoidHom.mem_ker, d2Hom_eq_zero_iff, ← isCocycle2_iff_d2Fun]

@[simp] lemma mem_B2 {f : Cochain2 G M} : f ∈ B2 G M ↔ ∃ g : Cochain1 G M, d1Hom G M g = f :=
  AddMonoidHom.mem_range

lemma B1_le_Z1 : B1 G M ≤ Z1 G M := by
  rintro f ⟨m, rfl⟩
  rw [mem_Z1]
  intro σ τ
  simp only [d0Hom_apply]
  rw [smul_sub, mul_smul]
  abel

lemma B2_le_Z2 : B2 G M ≤ Z2 G M := by
  rintro f ⟨g, rfl⟩
  rw [mem_Z2]
  intro σ τ ρ
  simp only [d1Hom_apply]
  rw [smul_add, smul_sub, mul_smul, mul_assoc]
  abel

end Cohomology

/-! ### `H⁰`, `H¹`, `H²` -/

section Groups

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- `H⁰(G,M) = M^G`, as a subgroup of `M`. -/
def fixedPoints (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup M where
  carrier := {m | ∀ σ : G, σ • m = m}
  zero_mem' := by simp
  add_mem' := by
    intro m n hm hn σ
    rw [smul_add, hm σ, hn σ]
  neg_mem' := by
    intro m hm σ
    rw [smul_neg, hm σ]

@[simp] lemma mem_fixedPoints {m : M} : m ∈ fixedPoints G M ↔ ∀ σ : G, σ • m = m := Iff.rfl

/-- `H⁰(G,M) = M^G`, the invariants. -/
abbrev H0 (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]
    [DistribMulAction G M] : Type _ := ↥(fixedPoints G M)

end Groups

section CohomologyGroups

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]

/-- `B¹` viewed inside `Z¹`. -/
def B1' (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Z1 G M) := (B1 G M).comap (Z1 G M).subtype

/-- `B²` viewed inside `Z²`. -/
def B2' (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] :
    AddSubgroup (Z2 G M) := (B2 G M).comap (Z2 G M).subtype

@[simp] lemma mem_B1' {z : Z1 G M} : z ∈ B1' G M ↔ (z : Cochain1 G M) ∈ B1 G M :=
  Iff.rfl

@[simp] lemma mem_B2' {z : Z2 G M} : z ∈ B2' G M ↔ (z : Cochain2 G M) ∈ B2 G M :=
  Iff.rfl

/-- `H¹(G,M)`: continuous crossed homomorphisms modulo principal ones. -/
noncomputable abbrev H1 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] : Type _ :=
  (Z1 G M) ⧸ (B1' G M)

/-- `H²(G,M)`: continuous factor systems modulo `2`-coboundaries. -/
noncomputable abbrev H2 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M] : Type _ :=
  (Z2 G M) ⧸ (B2' G M)

/-- The class of a `1`-cocycle in `H¹`. -/
def H1.mk (z : Z1 G M) : H1 G M := QuotientAddGroup.mk z

/-- The class of a `2`-cocycle in `H²`. -/
def H2.mk (z : Z2 G M) : H2 G M := QuotientAddGroup.mk z

lemma H1.mk_eq_mk_iff (z w : Z1 G M) : H1.mk z = H1.mk w ↔ z - w ∈ B1' G M :=
  QuotientAddGroup.eq_iff_sub_mem

lemma H2.mk_eq_mk_iff (z w : Z2 G M) : H2.mk z = H2.mk w ↔ z - w ∈ B2' G M :=
  QuotientAddGroup.eq_iff_sub_mem

@[simp] lemma H1.mk_zero : H1.mk (0 : Z1 G M) = 0 := rfl

@[simp] lemma H2.mk_zero : H2.mk (0 : Z2 G M) = 0 := rfl

lemma H1.mk_eq_zero_iff (z : Z1 G M) : H1.mk z = 0 ↔ z ∈ B1' G M := by
  rw [← H1.mk_zero (G := G) (M := M), H1.mk_eq_mk_iff]
  simp

lemma H2.mk_eq_zero_iff (z : Z2 G M) : H2.mk z = 0 ↔ z ∈ B2' G M := by
  rw [← H2.mk_zero (G := G) (M := M), H2.mk_eq_mk_iff]
  simp

end CohomologyGroups

end Work.ConCohomology
