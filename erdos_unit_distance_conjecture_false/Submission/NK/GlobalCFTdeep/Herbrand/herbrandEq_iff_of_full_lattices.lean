import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.StableRep
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_iff_of_finite_quotient
import Submission.NK.GlobalCFTdeep.Herbrand.exists_nat_smul_mem_of_span_eq_top

/-!
# Two full `G`-stable lattices have the same Herbrand quotient

Milne, *Class Field Theory*, Lemmas 3.4–3.5: if `L₁` and `L₂` are two full `G`-stable lattices in
the same `ℚ[G]`-module `A` (i.e. finitely generated `ℤ`-modules stable under `G` whose `ℚ`-span is
all of `A`), then `L₁` and `L₂` have the same Herbrand quotient.

Since both lattices are full in the same `ℚ`-vector space, they are commensurable: there is a
nonzero natural number `n` with `n • L₁ ⊆ L₂` (and symmetrically), so that the common sublattice
`D = L₁ ⊓ L₂` has finite index in each of them.  The invariance of the Herbrand quotient under a
finite-index extension (`Herbrand/herbrandEq_iff_of_finite_quotient`) applied to the two short exact
sequences `0 → D → L₁ → L₁/D → 0` and `0 → D → L₂ → L₂/D → 0` then gives the result.

## Implementation notes

The `ℤ`-module structure on the carrier of a `Rep ℤ G` is a (propositionally unique) diamond, and
instance synthesis does not always see through it.  All the `Submodule`/`Rep.quotient`/`Rep.ofHom`
manipulations below are therefore performed with `backward.isDefEq.respectTransparency` disabled
(the same device Mathlib uses to define `Representation.subrepresentation`).
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

/-- The additive injection `D ↪ L` induced by a subgroup inclusion `D ≤ L`, as a `ℤ`-linear map. -/
def inclusionMap {A : Type} [AddCommGroup A] (D L : AddSubgroup A) (hle : D ≤ L) :
    ↥D →ₗ[ℤ] ↥L :=
  (AddSubgroup.inclusion hle : ↥D →+ ↥L).toIntLinearMap

@[simp] lemma inclusionMap_apply {A : Type} [AddCommGroup A] (D L : AddSubgroup A)
    (hle : D ≤ L) (y : ↥D) : ((inclusionMap D L hle y : ↥L) : A) = (y : A) := rfl

/-- A subgroup of a finitely generated `ℤ`-module is finitely generated. -/
lemma moduleFinite_subgroup_of_le {A : Type} [AddCommGroup A] (D L : AddSubgroup A)
    (hle : D ≤ L) [Module.Finite ℤ ↥L] : Module.Finite ℤ ↥D := by
  let ι : ↥D →ₗ[ℤ] ↥L := inclusionMap D L hle
  have hι : Function.Injective ι := fun a b h => Subtype.ext (by
    simpa [ι] using congrArg (fun z : ↥L => (z : A)) h)
  haveI : IsNoetherian ℤ ↥L := isNoetherian_of_isNoetherianRing_of_finite ℤ ↥L
  have hfg : ι.range.FG := IsNoetherian.noetherian _
  haveI : Module.Finite ℤ ↥ι.range := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.equiv (LinearEquiv.ofInjective ι hι).symm

/-- If a nonzero integer carries `L` into `D ≤ L`, then `L ⧸ D` is finite. -/
lemma finite_quotient_of_smul_mem {A : Type} [AddCommGroup A] (D L : AddSubgroup A)
    (hle : D ≤ L) [Module.Finite ℤ ↥L]
    (n : ℤ) (hn : n ≠ 0) (h : ∀ x ∈ L, n • x ∈ D) :
    Finite (↥L ⧸ (inclusionMap D L hle).range) := by
  haveI hfg : Module.Finite ℤ (↥L ⧸ (inclusionMap D L hle).range) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have htor : IsAddTorsion (↥L ⧸ (inclusionMap D L hle).range) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (inclusionMap D L hle).range q
    rw [isOfFinAddOrder_iff_zsmul_eq_zero]
    refine ⟨n, hn, ?_⟩
    rw [← map_zsmul (Submodule.mkQ (inclusionMap D L hle).range) n x]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨⟨(n • (x : A)), h (x : A) x.2⟩, by ext; rfl⟩
  haveI : AddGroup.FG (↥L ⧸ (inclusionMap D L hle).range) :=
    Module.Finite.iff_addGroup_fg.mp hfg
  exact AddCommGroup.finite_of_fg_isAddTorsion _ htor

/-- **Herbrand's lemma for a subgroup of finite index.**  If `D ≤ L` are `G`-stable additive
subgroups of `A` with `L ⧸ D` finite, then `D` and `L` have the same Herbrand quotient. -/
theorem herbrandEq_iff_of_inclusion_finite {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    {A : Type} [AddCommGroup A] [Module ℚ A] [DistribMulAction G A] [SMulCommClass G ℚ A]
    (D L : AddSubgroup A) (hD : ∀ (g : G) {x : A}, x ∈ D → g • x ∈ D)
    (hL : ∀ (g : G) {x : A}, x ∈ L → g • x ∈ L) (hle : D ≤ L)
    [Module.Finite ℤ ↥L]
    (hfin : Finite (↥L ⧸ (inclusionMap D L hle).range))
    (m : ℕ) :
    HerbrandEq (repOfStableAddSubgroup D hD) m ↔ HerbrandEq (repOfStableAddSubgroup L hL) m := by
  have hW : ∀ g : G, (inclusionMap D L hle).range ≤
      (inclusionMap D L hle).range.comap ((repOfStableAddSubgroup L hL).ρ g) := by
    intro g x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨g • (y : A), hD g y.2⟩, by ext; rfl⟩
  let X₃ : Rep ℤ G := (repOfStableAddSubgroup L hL).quotient (inclusionMap D L hle).range hW
  let f : repOfStableAddSubgroup D hD ⟶ repOfStableAddSubgroup L hL :=
    Rep.ofHom ⟨inclusionMap D L hle, by intro g; ext y; rfl⟩
  let g : repOfStableAddSubgroup L hL ⟶ X₃ :=
    Rep.ofHom ⟨Submodule.mkQ (inclusionMap D L hle).range, by intro gg; ext y; rfl⟩
  let S : ShortComplex (Rep ℤ G) := ShortComplex.mk f g (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    change Submodule.mkQ (inclusionMap D L hle).range (inclusionMap D L hle y) = 0
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩)
  have hS : S.ShortExact := by
    refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise S
      ((Rep.mono_iff_injective S.f).2 ?_) ((Rep.epi_iff_surjective S.g).2 ?_) ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun z : ↥L => (z : A)) hab)
    · intro y
      exact Submodule.mkQ_surjective (inclusionMap D L hle).range y
    · intro x hx
      have hx'' : x ∈ (inclusionMap D L hle).range := (Submodule.Quotient.mk_eq_zero _).mp hx
      obtain ⟨y, rfl⟩ := hx''
      exact ⟨y, rfl⟩
  haveI h2 : Module.Finite ℤ S.X₂.V := ‹Module.Finite ℤ ↥L›
  haveI h3 : Module.Finite ℤ S.X₁.V := moduleFinite_subgroup_of_le D L hle
  haveI h4 : Finite ↥S.X₃ := hfin
  haveI h5 : Module.Finite ℤ S.X₃.V := by
    have := h4; exact Module.Finite.of_finite
  haveI : Finite ↥(tateCohomology S.X₁ 0) := (finite_tateCohomology_of_moduleFinite S.X₁).1
  haveI : Finite ↥(tateCohomology S.X₁ 1) := (finite_tateCohomology_of_moduleFinite S.X₁).2
  haveI : Finite ↥(tateCohomology S.X₂ 0) := (finite_tateCohomology_of_moduleFinite S.X₂).1
  haveI : Finite ↥(tateCohomology S.X₂ 1) := (finite_tateCohomology_of_moduleFinite S.X₂).2
  haveI : Finite ↥(tateCohomology S.X₃ 0) := (finite_tateCohomology_of_moduleFinite S.X₃).1
  haveI : Finite ↥(tateCohomology S.X₃ 1) := (finite_tateCohomology_of_moduleFinite S.X₃).2
  exact herbrandEq_iff_of_finite_quotient S hS m

/-- Two full `G`-stable lattices in the same `ℚ[G]`-module have the same Herbrand quotient (Milne, CFT, Lemmas 3.4-3.5). -/
theorem herbrandEq_iff_of_full_lattices {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    {A : Type} [AddCommGroup A] [Module ℚ A] [DistribMulAction G A] [SMulCommClass G ℚ A]
    (L₁ L₂ : AddSubgroup A) (h1 : ∀ (g : G) {x : A}, x ∈ L₁ → g • x ∈ L₁)
    (h2 : ∀ (g : G) {x : A}, x ∈ L₂ → g • x ∈ L₂)
    [Module.Finite ℤ ↥L₁] [Module.Finite ℤ ↥L₂]
    (hsp1 : Submodule.span ℚ (L₁ : Set A) = ⊤) (hsp2 : Submodule.span ℚ (L₂ : Set A) = ⊤)
    (m : ℕ) :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.repOfStableAddSubgroup L₁ h1) m ↔
      NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.repOfStableAddSubgroup L₂ h2) m := by
  have hD : ∀ (g : G) {x : A}, x ∈ L₁ ⊓ L₂ → g • x ∈ L₁ ⊓ L₂ := by
    intro g x hx
    exact ⟨h1 g hx.1, h2 g hx.2⟩
  haveI hDfin : Module.Finite ℤ ↥(L₁ ⊓ L₂) := moduleFinite_subgroup_of_le _ _ inf_le_left
  obtain ⟨n₁, hn₁, h1n⟩ := exists_nat_smul_mem_of_span_eq_top L₁ L₂ hsp2
  obtain ⟨n₂, hn₂, h2n⟩ := exists_nat_smul_mem_of_span_eq_top L₂ L₁ hsp1
  haveI hfin1 : Finite (↥L₁ ⧸ (inclusionMap (L₁ ⊓ L₂) L₁ inf_le_left).range) :=
    finite_quotient_of_smul_mem (L₁ ⊓ L₂) L₁ inf_le_left (n₁ : ℤ)
      (Int.natCast_ne_zero.mpr hn₁) (fun x hx => ⟨L₁.zsmul_mem hx _, h1n x hx⟩)
  haveI hfin2 : Finite (↥L₂ ⧸ (inclusionMap (L₁ ⊓ L₂) L₂ inf_le_right).range) :=
    finite_quotient_of_smul_mem (L₁ ⊓ L₂) L₂ inf_le_right (n₂ : ℤ)
      (Int.natCast_ne_zero.mpr hn₂) (fun x hx => ⟨h2n x hx, L₂.zsmul_mem hx _⟩)
  have hA := herbrandEq_iff_of_inclusion_finite (L₁ ⊓ L₂) L₁ hD h1 inf_le_left
    (m := m) hfin1
  have hB := herbrandEq_iff_of_inclusion_finite (L₁ ⊓ L₂) L₂ hD h2 inf_le_right
    (m := m) hfin2
  exact hA.symm.trans hB

end NK.GlobalCFTdeep.Herbrand
