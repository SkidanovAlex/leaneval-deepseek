import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_H1_coind
import Submission.Work.SSGRoute.subsingleton_H1_pi_inf
import Submission.Work.SSGRoute.homCoind_H1_free
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹` of a coinduced module, restricted to a subgroup

Let `G` be a group, `H ≤ G` a subgroup, `A` a module for a group `D`, and `p : D →* G` a
homomorphism whose image is exactly `H`.  The `D`-module `G → A` with the coinduced action
`(δ · f) g = δ • f ((p δ)⁻¹ * g)` is, restricted to `D`, a product of copies of `H → A`
(one for each left coset `Hg ∈ H \ G`), because `D` acts on `G` through `H` by left
multiplication and thereby preserves every coset.

This is the subgroup form of `Work.SSGRoute.coindU_H1_subsingleton_v2` (the full-group case
`D = Gal(Ω/k)`, `H = Gal(K/k)`), whose proof needs the vanishing over the *fixing subgroup*
`Gal(Ω/K)`; here the relevant subgroup is `ker p = D ⊓ Gal(Ω/K)`, a closed subgroup of `D`.

## Main results

* `selfProdLeftCosets` — the `H`-equivariant bijection `G ≃ H × (H \ G)` (`H` acting by left
  multiplication on itself and trivially on `H \ G`);
* `CoindArrow.equivPiLeftCosets` — the equivariant additive equivalence
  `(G → A) ≃+ (H \ G → (H → A))` for the coinduced actions, with the equivariance
  `CoindArrow.equivPiLeftCosets_smul`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

open scoped Classical

universe u v w

noncomputable section

/-! ## A universe-polymorphic form of `H¹` of a product

`Work.SSGRoute.subsingleton_H1_pi_inf` is stated with all types in `Type 0`; the modules of the
present file live in higher universes, so we replay its (short) proof here. -/

/-- **`H¹` of an arbitrary product of coefficient modules is a subsingleton as soon as each factor
is** (universe-polymorphic form of `Work.SSGRoute.subsingleton_H1_pi_inf`). -/
theorem subsingleton_H1_pi_inf' {Γ : Type u} [TopologicalSpace Γ] [Group Γ]
    {ι : Type v} {X : ι → Type w} [∀ i, AddCommGroup (X i)] [∀ i, DistribMulAction Γ (X i)]
    (h : ∀ i, Subsingleton (Work.AbsoluteKummer.H1 Γ (X i))) :
    Subsingleton (@Work.AbsoluteKummer.H1 Γ (∀ i, X i) _ _
      Pi.addCommGroup (Pi.distribMulAction Γ)) := by
  classical
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨F, hF⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 Γ (∀ i, X i)).comap
      (Work.AbsoluteKummer.Z1 Γ (∀ i, X i)).subtype) x
  rw [show x = Work.AbsoluteKummer.H1π Γ (∀ i, X i) F from hF.symm,
    Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff]
  have key : ∀ i, ∃ a : X i,
      Work.GroupCohomology.d0 Γ (X i) a = fun σ : Γ => (F : Γ → ∀ i, X i) σ i := by
    intro i
    have hsub : Subsingleton (Work.AbsoluteKummer.H1 Γ (X i)) := h i
    have hmem : (fun σ : Γ => (F : Γ → ∀ i, X i) σ i) ∈
        Work.AbsoluteKummer.Z1 Γ (X i) := by
      obtain ⟨hcross, hloc⟩ :=
        (Work.AbsoluteKummer.mem_Z1_iff (G := Γ) (M := ∀ i, X i)
          (f := (F : Γ → ∀ i, X i))).mp F.2
      rw [Work.AbsoluteKummer.mem_Z1_iff]
      exact ⟨fun g hh => by
          have h2 := congrFun (hcross g hh) i
          simpa using h2,
        Work.AbsoluteKummer.IsLocallyConstant.map (fun v : ∀ i, X i => v i) hloc⟩
    have hz : Work.AbsoluteKummer.H1π Γ (X i) ⟨_, hmem⟩ = 0 := Subsingleton.elim _ _
    rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff] at hz
    exact hz
  choose a ha using key
  exact ⟨a, by
    funext σ i
    have h2 := congrFun (ha i) σ
    simp only [Work.GroupCohomology.d0_apply] at h2
    show (σ • a - a) i = (F : Γ → ∀ i, X i) σ i
    rw [Pi.sub_apply, Pi.smul_apply]
    exact h2⟩

/-! ## The coset decomposition of a group as an `H`-set -/

section Coset

variable {G : Type*} [Group G]

/-- The setoid of the left cosets `Hg` of a subgroup `H` of a group `G`. -/
def leftCosetSetoid (H : Subgroup G) : Setoid G where
  r a b := a * b⁻¹ ∈ H
  iseqv := by
    refine ⟨fun a => by simp, fun {a b} hab => ?_, fun {a b c} hab hbc => ?_⟩
    · simpa [mul_inv_rev, inv_inv] using H.inv_mem hab
    · have h : a * b⁻¹ * (b * c⁻¹) ∈ H := H.mul_mem hab hbc
      simpa [mul_assoc] using h

/-- The set of left cosets `H \ G`. -/
abbrev LeftCosets (H : Subgroup G) : Type _ := Quotient (leftCosetSetoid H)

/-- The quotient map onto the coset space. -/
abbrev leftCosetMk (H : Subgroup G) (g : G) : LeftCosets H := Quotient.mk (leftCosetSetoid H) g

/-- Membership form of the equality of cosets. -/
theorem leftCosetMk_eq_iff {H : Subgroup G} {a b : G} :
    leftCosetMk H a = leftCosetMk H b ↔ a * b⁻¹ ∈ H :=
  Quotient.eq

/-- The chosen lift of a coset represents it. -/
theorem leftCosetMk_out (H : Subgroup G) (q : LeftCosets H) :
    leftCosetMk H (Quotient.out q) = q := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep q
  rw [← ha, leftCosetMk_eq_iff]
  exact Quotient.mk_out (s := leftCosetSetoid H) a

/-- **Left multiplication by an element of `H` does not change the coset.** -/
theorem leftCosetMk_mul (H : Subgroup G) (h : H) (g : G) :
    leftCosetMk H ((h : G) * g) = leftCosetMk H g :=
  leftCosetMk_eq_iff.mpr (by simpa [mul_assoc] using h.2)

/-- **A group is the product of a subgroup and its coset space**, `H`-equivariantly: an element of
`G` is `h · (a lift of its coset)`, and the coset is unchanged by left multiplication by `H`. -/
noncomputable def selfProdLeftCosets (H : Subgroup G) : G ≃ H × LeftCosets H where
  toFun g := (⟨g * (Quotient.out (leftCosetMk H g))⁻¹, by
      have h := Quotient.mk_out (s := leftCosetSetoid H) g
      simpa [mul_inv_rev, inv_inv] using H.inv_mem h⟩, leftCosetMk H g)
  invFun x := (x.1 : G) * Quotient.out x.2
  left_inv := by
    intro g
    show (g * (Quotient.out (leftCosetMk H g))⁻¹) * Quotient.out (leftCosetMk H g) = g
    group
  right_inv := by
    rintro ⟨⟨h, hh⟩, q⟩
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      have h1 : leftCosetMk H ((h : G) * Quotient.out q) = q := by
        rw [leftCosetMk_mul (H := H) ⟨h, hh⟩ (Quotient.out q)]
        exact leftCosetMk_out H q
      show ((h : G) * Quotient.out q)
        * (Quotient.out (leftCosetMk H ((h : G) * Quotient.out q)))⁻¹ = h
      rw [h1]
      group
    · have h1 : leftCosetMk H ((h : G) * Quotient.out q) = q := by
        rw [leftCosetMk_mul (H := H) ⟨h, hh⟩ (Quotient.out q)]
        exact leftCosetMk_out H q
      show leftCosetMk H ((h : G) * Quotient.out q) = q
      exact h1

/-- **The coset decomposition is `H`-equivariant.** -/
theorem selfProdLeftCosets_mul (H : Subgroup G) (h : H) (g : G) :
    selfProdLeftCosets H ((h : G) * g)
      = (h * (selfProdLeftCosets H g).1, (selfProdLeftCosets H g).2) := by
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    have h1 : leftCosetMk H ((h : G) * g) = leftCosetMk H g := leftCosetMk_mul H h g
    show ((h : G) * g) * (Quotient.out (leftCosetMk H ((h : G) * g)))⁻¹
      = (h : G) * (g * (Quotient.out (leftCosetMk H g))⁻¹)
    rw [h1]
    group
  · show leftCosetMk H ((h : G) * g) = leftCosetMk H g
    exact leftCosetMk_mul H h g

/-- The `H`-component of the lift of a coset is trivial. -/
theorem selfProdLeftCosets_out (H : Subgroup G) (q : LeftCosets H) :
    (selfProdLeftCosets H (Quotient.out q)).1 = 1 := by
  refine Subtype.ext ?_
  show Quotient.out q * (Quotient.out (leftCosetMk H (Quotient.out q)))⁻¹ = 1
  rw [leftCosetMk_out H q]
  group

/-- The two components of the coset decomposition reconstruct the element. -/
theorem selfProdLeftCosets_apply (H : Subgroup G) (g : G) :
    ((selfProdLeftCosets H g).1 : G) * Quotient.out ((selfProdLeftCosets H g).2) = g :=
  (selfProdLeftCosets H).symm_apply_apply g

end Coset

/-! ## The coinduced action on `G → A` and the product decomposition -/

section CoindArrow

variable {D : Type u} {G : Type v} {A : Type w}

/-- The module `G → A` with the coinduced action of `D` along `p : D →* G`,
`(δ · f) g = δ • f ((p δ)⁻¹ * g)`.  It is a plain `def` (not `abbrev`/`@[reducible]`) so that
instance search does **not** unfold it into the Pi type `G → A`: otherwise the instance below
matches arbitrary function types and the search diverges. -/
def CoindArrow (D : Type u) [Group D] (G : Type v) [Group G] (A : Type w)
    [AddCommGroup A] (p : D →* G) [DistribMulAction D A] : Type (max v w) := G → A

namespace CoindArrow

variable [Group D] [Group G] [AddCommGroup A] {p : D →* G} [DistribMulAction D A]

instance instAddCommGroup : AddCommGroup (CoindArrow D G A p) :=
  inferInstanceAs (AddCommGroup (G → A))

/-- `CoindArrow` is a function type, up to the (non-reducible) wrapper. -/
instance instCoeFun : CoeFun (CoindArrow D G A p) (fun _ => G → A) := ⟨fun f => f⟩

instance instSMul : SMul D (CoindArrow D G A p) :=
  ⟨fun δ f g => δ • f ((p δ)⁻¹ * g)⟩

theorem smul_apply (δ : D) (f : CoindArrow D G A p) (g : G) :
    (δ • f) g = δ • f ((p δ)⁻¹ * g) := rfl

instance instDistribMulAction : DistribMulAction D (CoindArrow D G A p) where
  one_smul f := by
    funext g
    rw [smul_apply, map_one, inv_one, one_mul, one_smul]
  mul_smul δ ε f := by
    funext g
    rw [smul_apply, smul_apply, map_mul, mul_inv_rev, mul_assoc, smul_apply]
    exact mul_smul δ ε (f ((p ε)⁻¹ * ((p δ)⁻¹ * g)))
  smul_zero δ := by
    funext g
    show δ • (0 : A) = (0 : A)
    exact smul_zero δ
  smul_add δ f f' := by
    funext g
    show δ • (f ((p δ)⁻¹ * g) + f' ((p δ)⁻¹ * g))
      = δ • f ((p δ)⁻¹ * g) + δ • f' ((p δ)⁻¹ * g)
    rw [smul_add]

attribute [local instance 10000] CoindArrow.instAddCommGroup CoindArrow.instDistribMulAction

/-- The component of `f` on the coset `x`, as a function on `p.range`. -/
def comp (f : CoindArrow D G A p) (x : LeftCosets p.range) :
    CoindArrow D p.range A p.rangeRestrict :=
  fun h => f ((h : G) * Quotient.out x)

theorem comp_apply (f : CoindArrow D G A p) (x : LeftCosets p.range) (h : p.range) :
    comp f x h = f ((h : G) * Quotient.out x) := rfl

/-- The coinduction `D/ker p ≅ p.range` is compatible with the two actions on `A`. -/
theorem rangeRestrict_inv_mul_eq (δ : D) (h : p.range) :
    ((p.rangeRestrict δ)⁻¹ * h : p.range)
      = ⟨(p δ)⁻¹ * (h : G), p.range.mul_mem
          (p.range.inv_mem (MonoidHom.mem_range.mpr ⟨δ, rfl⟩)) h.2⟩ :=
  Subtype.ext rfl

/-- **The components are equivariant.** -/
theorem comp_smul (δ : D) (f : CoindArrow D G A p) (x : LeftCosets p.range) :
    comp (δ • f) x = δ • comp f x := by
  funext h
  show δ • f ((p δ)⁻¹ * ((h : G) * Quotient.out x))
    = δ • f ((((p.rangeRestrict δ)⁻¹ * h : p.range) : G) * Quotient.out x)
  rw [rangeRestrict_inv_mul_eq, mul_assoc]

/-- The reconstruction of `f` from its components. -/
def compInv (F : LeftCosets p.range → CoindArrow D p.range A p.rangeRestrict) :
    CoindArrow D G A p :=
  fun g => F (leftCosetMk p.range g) ((selfProdLeftCosets p.range g).1)

theorem compInv_apply (F : LeftCosets p.range → CoindArrow D p.range A p.rangeRestrict) (g : G) :
    compInv F g = F (leftCosetMk p.range g) ((selfProdLeftCosets p.range g).1) := rfl

theorem comp_compInv (f : CoindArrow D G A p) :
    compInv (fun x => comp f x) = f := by
  funext g
  rw [compInv_apply]
  exact congrArg f (selfProdLeftCosets_apply p.range g)

theorem compInv_comp (F : LeftCosets p.range → CoindArrow D p.range A p.rangeRestrict) :
    (fun x => comp (compInv F) x) = F := by
  funext x h
  rw [comp_apply, compInv_apply]
  have h1 : leftCosetMk p.range ((h : G) * Quotient.out x) = x := by
    rw [leftCosetMk_mul p.range h (Quotient.out x)]
    exact leftCosetMk_out p.range x
  have h2 : (selfProdLeftCosets p.range ((h : G) * Quotient.out x)).1 = h := by
    rw [selfProdLeftCosets_mul p.range h (Quotient.out x),
      selfProdLeftCosets_out p.range x, mul_one]
  rw [h1, h2]

/-- **The coinduced module is the product of the coinduced modules of the cosets**: the `D`-orbits
of `G` are the left `p.range`-cosets, each with stabiliser `ker p`. -/
noncomputable def equivPiLeftCosets (p : D →* G) :
    CoindArrow D G A p ≃+ (LeftCosets p.range → CoindArrow D p.range A p.rangeRestrict) where
  toFun f := fun x => comp f x
  invFun F := compInv F
  left_inv f := comp_compInv f
  right_inv F := compInv_comp F
  map_add' f f' := by
    funext x h
    rfl

theorem equivPiLeftCosets_apply (p : D →* G) (f : CoindArrow D G A p)
    (x : LeftCosets p.range) (h : p.range) :
    equivPiLeftCosets (A := A) p f x h = f ((h : G) * Quotient.out x) := rfl

/-- **The product decomposition is equivariant.** -/
theorem equivPiLeftCosets_smul (p : D →* G) (δ : D) (f : CoindArrow D G A p) :
    equivPiLeftCosets (A := A) p (δ • f)
      = fun x => δ • (equivPiLeftCosets (A := A) p f x) := by
  funext x
  exact comp_smul δ f x

/-! ### The identification with the coinduced module `Coind_D^{ker p} A` -/

/-- A choice of a preimage in `D` of an element of `p.range`. -/
noncomputable def preimage (h : p.range) : D := Classical.choose h.2

theorem rangeRestrict_preimage (h : p.range) : p.rangeRestrict (preimage h) = h :=
  Subtype.ext (Classical.choose_spec h.2)

theorem map_preimage (h : p.range) : p (preimage h) = (h : G) :=
  congrArg Subtype.val (rangeRestrict_preimage (p := p) h)

theorem rangeRestrict_coe (δ : D) : ((p.rangeRestrict δ : p.range) : G) = p δ := rfl

/-- **The coinduced module on `p.range` is the coinduced module from `ker p`.**  Sending `ψ` to
`δ ↦ δ⁻¹ • ψ (p δ)` is a `D`-equivariant additive equivalence
`(p.range → A) ≃+ Coind_D^{ker p} A`; the inverse evaluates at a chosen preimage. -/
noncomputable def toCoind : CoindArrow D p.range A p.rangeRestrict ≃+ Coind D p.ker A where
  toFun ψ := ⟨fun δ => δ⁻¹ • ψ (p.rangeRestrict δ), by
    intro δ u
    have hu : p.rangeRestrict (u : D) = 1 := by
      refine Subtype.ext ?_
      show p (u : D) = 1
      exact u.2
    show (δ * (u : D))⁻¹ • ψ (p.rangeRestrict (δ * (u : D)))
      = (u : D)⁻¹ • (δ⁻¹ • ψ (p.rangeRestrict δ))
    rw [map_mul, hu, mul_one, mul_inv_rev, mul_smul]⟩
  invFun F := fun h => preimage h • (F (preimage h))
  map_add' ψ ψ' := by
    refine Subtype.ext (funext fun δ => ?_)
    show δ⁻¹ • (ψ (p.rangeRestrict δ) + ψ' (p.rangeRestrict δ))
      = δ⁻¹ • ψ (p.rangeRestrict δ) + δ⁻¹ • ψ' (p.rangeRestrict δ)
    rw [smul_add]
  left_inv ψ := by
    funext h
    show preimage h • (preimage h)⁻¹ • ψ (p.rangeRestrict (preimage h)) = ψ h
    rw [rangeRestrict_preimage, ← mul_smul]
    simp
  right_inv F := by
    refine Subtype.ext (funext fun δ => ?_)
    show (δ⁻¹) • (preimage (p.rangeRestrict δ) • F (preimage (p.rangeRestrict δ))) = F δ
    have hmem : δ⁻¹ * preimage (p.rangeRestrict δ) ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_preimage, rangeRestrict_coe, inv_mul_cancel]
    have h2 : F (preimage (p.rangeRestrict δ))
        = (δ⁻¹ * preimage (p.rangeRestrict δ))⁻¹ • F δ := by
      have h := F.2 δ (⟨δ⁻¹ * preimage (p.rangeRestrict δ), hmem⟩ : p.ker)
      rw [show δ * ((⟨δ⁻¹ * preimage (p.rangeRestrict δ), hmem⟩ : p.ker) : D)
        = preimage (p.rangeRestrict δ) from by
          show δ * (δ⁻¹ * preimage (p.rangeRestrict δ)) = preimage (p.rangeRestrict δ)
          group] at h
      exact h
    rw [h2, ← mul_smul, ← mul_smul]
    simp

theorem toCoind_smul (δ : D) (ψ : CoindArrow D p.range A p.rangeRestrict) :
    toCoind (A := A) (p := p) (δ • ψ) = δ • toCoind (A := A) (p := p) ψ := by
  refine Subtype.ext (funext fun ε => ?_)
  show (ε⁻¹) • (δ • ψ ((p.rangeRestrict δ)⁻¹ * p.rangeRestrict ε))
    = (δ⁻¹ * ε)⁻¹ • ψ (p.rangeRestrict (δ⁻¹ * ε))
  rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_smul]

/-- **`H¹(D, G → A) = 0`** when `D` acts on `G` through `p`, `ker p` is open of finite index and
`H¹(ker p, A) = 0`. -/
theorem subsingleton_H1_coindArrow {D G : Type*} [Group D] [TopologicalSpace D]
    [IsTopologicalGroup D] [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction D A]
    {p : D →* G} (hopen : IsOpen (p.ker : Set D)) [p.ker.FiniteIndex]
    (hdis : Work.AbsoluteKummer.IsDiscreteModule ↥(p.ker) A)
    (hker : Subsingleton (Work.AbsoluteKummer.H1 ↥(p.ker) A)) :
    Subsingleton (Work.AbsoluteKummer.H1 D (CoindArrow D G A p)) := by
  refine @Work.SSGRoute.subsingleton_H1_of_addEquiv D _ _ (CoindArrow D G A p)
    (LeftCosets p.range → CoindArrow D p.range A p.rangeRestrict)
    (CoindArrow.instAddCommGroup) (CoindArrow.instDistribMulAction)
    Pi.addCommGroup (Pi.distribMulAction D)
    (equivPiLeftCosets (A := A) p) (fun δ f => equivPiLeftCosets_smul p δ f) ?_
  refine @subsingleton_H1_pi_inf' D _ _ (LeftCosets p.range)
    (fun _ => CoindArrow D p.range A p.rangeRestrict)
    (fun _ => CoindArrow.instAddCommGroup) (fun _ => CoindArrow.instDistribMulAction) (fun x => ?_)
  obtain ⟨φ⟩ := shapiro_H1_coind (G := D) p.ker hopen hdis
  have hsub : Subsingleton (Work.AbsoluteKummer.H1 D (Coind D p.ker A)) :=
    ⟨fun a b => φ.injective (Subsingleton.elim (φ a) (φ b))⟩
  exact Work.SSGRoute.subsingleton_H1_of_addEquiv (toCoind (A := A) (p := p))
    (fun δ ψ => toCoind_smul δ ψ) hsub

end CoindArrow

end CoindArrow

/-! ## Injectivity of the connecting map of the dualised canonical resolution

The local data of a finite place (`k_v`, `M = localClosureAt`, `K'`) is *not* a number field, so
the E1a chapter uses the field-generic dualised resolution `PT.e1aSESgen`; the injectivity of its
connecting map (at the *full* group `Gal(M/k_v)`) is what the localisation comparison square
consumes.  Its kernel is `H¹(Gal(M/k_v), homCoindFreeT k_v M K' V.V)`, which vanishes by the
field-generic (full-group) Shapiro/Hilbert-90 `Work.SSGRoute.homCoind_H1_free_conj_v2`. -/

/-- **Injectivity of the connecting map of the field-generic dualised canonical resolution.** -/
theorem e1aSESgen_deltaH2_injective {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (V : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite V.V] :
    Function.Injective
      (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) V).deltaH2 := by
  haveI hsub : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K V.V)) :=
    Work.SSGRoute.homCoind_H1_free_conj_v2 (k := k) (Ω := Ω) (K := K) (ι := V.V)
  have hker := (Work.AbsoluteKummer.SES.range_mapH1_eq_ker_deltaH2
    (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) V)).symm
  intro x y hxy
  have hmem : x - y ∈ (Work.SSGRoute.PT.e1aSESgen (k := k) (Ω := Ω) (K := K) V).deltaH2.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
  rw [hker] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := Subsingleton.elim z 0
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

end

end Work.SSGRoute.PT
