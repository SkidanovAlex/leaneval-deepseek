import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_local

/-!
# The abelian case of the local norm index theorem (Neukirch–Uchida, local input)

This file is the requested lemma `natCard_quotient_units_range_norm_adicCompletion_of_commute`:

`|K_Qˣ ⧸ N_{L_q/K_Q} L_qˣ| = [L_q : K_Q]` for `L/K` a finite **abelian** Galois extension of
number fields and `q | Q`.  This is the abelian local norm index theorem, a theorem of local
class field theory, and it is TRUE.  **Do not `declare_false`.**

A complete route, with *no* invariant map and *no* profinite cohomology, is documented in
`Submission/Work/NumberTheory/NumberField/Completion/STATUS_of_commute_natCard.md` and
`.../NOTE_element_of_order_n.md`.  In outline:

* `P9`: for every intermediate `F ⊆ K ⊆ E := q.adicCompletion L`, `|H²(Gal(E/K), Eˣ)| = [E:K]`
  (induction: cyclic base case + degree-2 inflation–restriction multiplicativity);
* `P12`: `H²(Gal(E/K), Eˣ)` contains an element of order `[E:K]` (finite unramified twist:
  choose the unramified `K'/K` of degree `[E:K]`; the composite `Res∘Inf` on
  `H²(K'/K, K'ˣ) ≅ ℤ/[E:K]` is `×e` followed by reduction mod `[E'/E] = e`, hence `0`);
* `P13`: Tate's theorem (splitting module + two dimension shifts), giving
  `|Ĥ⁰(Gal(E/F), Eˣ)| = |Gal(E/F)ᵃᵇ| = [E:F]`;
* assembly with `natCard_tateCohomology_zero_units` and `IsGalois.card_aut_eq_finrank`.

The three lemmas `groupCohomologyResLinearEquiv`, `natCard_groupCohomology_res_mulEquiv` and
`subsingleton_groupCohomology_res_mulEquiv` below are the (proved) group-isomorphism invariance of
`groupCohomology` needed for the Galois-correspondence plumbing.
-/


/-! ## Helper: invariance of group cohomology under a group isomorphism

`groupCohomology` (Mathlib) is indexed by `Rep ℤ G`; the Galois-correspondence plumbing of the
local norm index theorem needs to compare `groupCohomology` of `Gal(E/B₁)` with that of a subgroup
`H ≤ Gal(E/B)` (and `Gal(B₁/B)` with `G ⧸ H`).  The cochain complexes differ only by the
reindexing `Fin n → G ≃ Fin n → G'`, which commutes with the differentials, so the cohomology
groups are isomorphic.  -/

open CategoryTheory groupCohomology in
/-- Reindexing of inhomogeneous cochains along a group isomorphism. -/
private noncomputable def cochainReindex (k : Type) [CommRing k] {G G' : Type} [Group G]
    [Group G'] (e : G ≃* G') (V : Type) [AddCommGroup V] [Module k V] (n : ℕ) :
    ((Fin n → G) → V) ≃ₗ[k] ((Fin n → G') → V) where
  toFun f := fun g' => f (fun i => e.symm (g' i))
  invFun f := fun g => f (fun i => e (g i))
  left_inv f := by funext g; simp
  right_inv f := by funext g; simp
  map_add' f₁ f₂ := by funext g; simp
  map_smul' c f := by funext g; simp

open CategoryTheory groupCohomology in
private lemma cochainReindex_apply (k : Type) [CommRing k] {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {V : Type} [AddCommGroup V] [Module k V] {n : ℕ}
    (f : (Fin n → G) → V) (g' : Fin n → G') :
    cochainReindex k e V n f g' = f (fun i => e.symm (g' i)) := rfl

open CategoryTheory groupCohomology in
private lemma contractNth_map {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {n : ℕ} (j : Fin (n+1)) (g' : Fin (n+1) → G') :
    Fin.contractNth j (· * ·) (fun i => e.symm (g' i)) =
      fun k => e.symm (Fin.contractNth j (· * ·) g' k) := by
  funext k
  simp only [Fin.contractNth]
  split_ifs <;> simp [map_mul]

open CategoryTheory groupCohomology in
private lemma inhomogeneousCochains_d_comm {k G G' : Type} [CommRing k] [Group G] [Group G']
    (e : G ≃* G') (A : Rep.{0,0,0} k G') (n : ℕ) (f : (Fin n → G) → A.V) :
    cochainReindex k e A.V (n+1)
        (inhomogeneousCochains.d (Rep.res e.toMonoidHom A) n f)
      = inhomogeneousCochains.d A n (cochainReindex k e A.V n f) := by
  funext g'
  show (A.ρ (e (e.symm (g' 0)))) (f (fun i => e.symm (g' i.succ))) +
      ∑ j : Fin (n+1), (-1 : k) ^ ((j : ℕ) + 1) •
        f (Fin.contractNth j (· * ·) (fun i => e.symm (g' i)))
    = (A.ρ (g' 0)) ((cochainReindex k e A.V n f) (fun i => g' i.succ)) +
      ∑ j : Fin (n+1), (-1 : k) ^ ((j : ℕ) + 1) •
        (cochainReindex k e A.V n f) (Fin.contractNth j (· * ·) g')
  rw [e.apply_symm_apply]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [cochainReindex_apply, contractNth_map]

open CategoryTheory groupCohomology in
private noncomputable def cochainComplexIso {k G G' : Type} [CommRing k] [Group G] [Group G']
    (e : G ≃* G') (A : Rep.{0,0,0} k G') :
    inhomogeneousCochains (Rep.res e.toMonoidHom A) ≅
      inhomogeneousCochains A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainReindex k e A.V n).toModuleIso)
    (fun i j hij => by
      have h : i + 1 = j := hij
      subst h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext g
      rw [inhomogeneousCochains.d_def A i,
        inhomogeneousCochains.d_def (Rep.res e.toMonoidHom A) i]
      exact (congrFun (inhomogeneousCochains_d_comm e A i x) g).symm)

open CategoryTheory groupCohomology in
/-- **Invariance of group cohomology under a group isomorphism** (linear-equivalence form).  For a
group isomorphism `e : G ≃* G'` and `A : Rep ℤ G'`, the cohomology of `A` and that of its pullback
`Rep.res e A` along `e` are isomorphic. -/
theorem groupCohomologyResLinearEquiv {k G G' : Type} [CommRing k] [Group G] [Group G']
    (e : G ≃* G') (A : Rep.{0,0,0} k G') (n : ℕ) :
    Nonempty (groupCohomology (Rep.res e.toMonoidHom A) n ≃ₗ[k] groupCohomology A n) :=
  ⟨((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
    (cochainComplexIso e A)).toLinearEquiv⟩

open CategoryTheory groupCohomology in
/-- Cardinality form. -/
theorem natCard_groupCohomology_res_mulEquiv {k G G' : Type} [CommRing k] [Group G] [Group G']
    (e : G ≃* G') (A : Rep.{0,0,0} k G') (n : ℕ) :
    Nat.card (groupCohomology (Rep.res e.toMonoidHom A) n) = Nat.card (groupCohomology A n) :=
  Nat.card_congr ((groupCohomologyResLinearEquiv e A n).some.toEquiv)

open CategoryTheory groupCohomology in
/-- `Subsingleton` form (used to transport Hilbert 90 across the Galois correspondence). -/
theorem subsingleton_groupCohomology_res_mulEquiv {k G G' : Type} [CommRing k] [Group G]
    [Group G'] (e : G ≃* G') (A : Rep.{0,0,0} k G') (n : ℕ) :
    Subsingleton (groupCohomology (Rep.res e.toMonoidHom A) n) ↔
      Subsingleton (groupCohomology A n) :=
  ((groupCohomologyResLinearEquiv e A n).some.toEquiv.subsingleton_congr)


/-! ## Helper: Galois correspondence for units and the `Rep.res` identification

Let `E/B` be a finite Galois extension of fields and `H ≤ Gal(E/B)`, `B₁ = E^H`.  The two
ingredients needed to compare `H²(Gal(E/B₁), Eˣ)` with the `H`-cohomology of `Eˣ` are

* `mem_invariants_iff`: `x : Eˣ` is fixed by all `h ∈ H` iff `x` comes from `B₁ˣ`;
* `res_subtype_eq_res_subgroupEquivAlgEquiv`: the `H`-action on `Eˣ` through `Gal(E/B)` *is* the
  action of `Gal(E/B₁)` read through `H ≃* Gal(E/B₁)` (`IntermediateField.subgroupEquivAlgEquiv`
  is the identity on underlying functions), so the two `Rep`s are equal. -/

open CategoryTheory Representation in
lemma subgroupEquivAlgEquiv_apply_coe {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) (h : H) :
    ⇑((IntermediateField.subgroupEquivAlgEquiv H) h) = ⇑(h : E ≃ₐ[B] E) := rfl

open CategoryTheory Representation in
/-- A unit of `E` is fixed by all of `H` iff it comes from the fixed field. -/
lemma mem_invariants_iff {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E)) (x : Eˣ) :
    (∀ h : H, (h : E ≃ₐ[B] E) • x = x) ↔
      x ∈ (Units.map (algebraMap ↥(IntermediateField.fixedField H) E).toMonoidHom).range := by
  set B₁ := IntermediateField.fixedField H with hB₁
  constructor
  · intro hx
    have hfix : ∀ h : H, (h : E ≃ₐ[B] E) (x : E) = (x : E) := by
      intro h
      have := congrArg (fun u : Eˣ => (u : E)) (hx h)
      simpa using this
    have hmem : (x : E) ∈ B₁ := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact hfix ⟨σ, hσ⟩
    refine ⟨Units.mk0 ⟨(x : E), hmem⟩ ?_, ?_⟩
    · exact fun h0 => Units.ne_zero x (Subtype.ext_iff.mp h0)
    · apply Units.ext
      rfl
  · rintro ⟨y, rfl⟩ h
    apply Units.ext
    have hy : (h : E ≃ₐ[B] E) (algebraMap ↥B₁ E (y : ↥B₁)) = algebraMap ↥B₁ E (y : ↥B₁) := by
      have hmem : (h : E ≃ₐ[B] E) ∈ IntermediateField.fixingSubgroup B₁ := by
        rw [hB₁, IntermediateField.fixingSubgroup_fixedField]; exact h.2
      exact (IntermediateField.mem_fixingSubgroup_iff B₁ _).mp hmem (y : ↥B₁) (y : ↥B₁).2
    simpa [Units.coe_smul, Units.coe_map] using hy


open CategoryTheory Representation in
/-- Bridge from `mem_invariants_iff` to the `Rep` language (needed for the
`quotientToInvariants` identification): the `H`-fixed elements of the units representation of
`E/B` are exactly the units of the fixed field `E^H`. -/
lemma mem_invariants_iff_repr {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E] (H : Subgroup (E ≃ₐ[B] E))
    (u : (Rep.ofAlgebraAutOnUnits B E).V) :
    (∀ h : H, (Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u = u) ↔
      ∃ y : (IntermediateField.fixedField H)ˣ,
        u = Additive.ofMul
          (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom y) := by
  set B₁ := IntermediateField.fixedField H with hB₁
  constructor
  · intro hu
    have hfix : ∀ h : H, (h : E ≃ₐ[B] E) • (Additive.toMul u : Eˣ) = (Additive.toMul u : Eˣ) := by
      intro h
      have h3 : Additive.toMul ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u) =
          Additive.toMul u := congrArg Additive.toMul (hu h)
      rwa [show Additive.toMul ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h) u) =
        (h : E ≃ₐ[B] E) • (Additive.toMul u : Eˣ) from rfl] at h3
    obtain ⟨y, hy⟩ := (mem_invariants_iff H (Additive.toMul u)).mp hfix
    refine ⟨y, ?_⟩
    rw [hy]
    rfl
  · rintro ⟨y, rfl⟩ h
    apply Additive.ofMul.injective
    show ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h))
        (Additive.ofMul (Units.map (algebraMap ↥B₁ E).toMonoidHom y)) =
      Additive.ofMul (Units.map (algebraMap ↥B₁ E).toMonoidHom y)
    rw [show ((Rep.ofAlgebraAutOnUnits B E).ρ (H.subtype h))
        (Additive.ofMul (Units.map (algebraMap ↥B₁ E).toMonoidHom y)) =
      Additive.ofMul ((h : E ≃ₐ[B] E) •
        ((Units.map (algebraMap ↥B₁ E).toMonoidHom y) : Eˣ)) from rfl]
    congr 1
    have hmem : (h : E ≃ₐ[B] E) ∈ IntermediateField.fixingSubgroup B₁ := by
      rw [hB₁, IntermediateField.fixingSubgroup_fixedField]; exact h.2
    have hy : (h : E ≃ₐ[B] E) (algebraMap ↥B₁ E (y : ↥B₁)) = algebraMap ↥B₁ E (y : ↥B₁) :=
      (IntermediateField.mem_fixingSubgroup_iff B₁ _).mp hmem (y : ↥B₁) (y : ↥B₁).2
    apply Units.ext
    simpa [Units.coe_map] using hy



open CategoryTheory groupCohomology in
/-- An isomorphism of `Rep`s induces an isomorphism on cohomology (and hence equal `Nat.card`). -/
theorem natCard_groupCohomology_iso {k G : Type} [CommRing k] [Group G]
    {A Bc : Rep.{0,0,0} k G} (e : A ≅ Bc) (n : ℕ) :
    Nat.card (groupCohomology A n) = Nat.card (groupCohomology Bc n) :=
  Nat.card_congr ((groupCohomology.functor k G n).mapIso e).toLinearEquiv.toEquiv

/-! ### The last piece of step 1

It remains to package the intertwining condition of `unitsInvLinearEquiv` into an isomorphism of
`Rep ℤ (Gal(E/B) ⧸ H)` between `(Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H` and
`Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
  (Rep.ofAlgebraAutOnUnits B ↥(E^H))`, i.e. to prove

```
lemma unitsInvLinearEquiv_equivariant (H : Subgroup (E ≃ₐ[B] E)) [H.Normal]
    (g : (E ≃ₐ[B] E) ⧸ H)
    (x : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    unitsInvLinearEquiv H (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ g x)
      = (Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
          (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))).ρ g
        (unitsInvLinearEquiv H x)
```

Proof plan (all pieces are in hand):

* the left action is `A.ρ g'` for a lift `g' : Gal(E/B)` of `g` (this is
  `Representation.ofQuotient (toInvariants A.ρ H) H`), the right action is `A₁.ρ (g'|E^H)`;
* both sides are units of `E^H` whose image under `Units.map (algebraMap (E^H) E)` is the same
  element of `Eˣ`: on the left that is `Additive.toMul (A.ρ g' x.1)`, on the right
  `g' (Additive.toMul x.1)`, and these agree because `Additive.toMul (A.ρ g' u) = g' u` for
  `u : A.V`;
* `Units.map (algebraMap (E^H) E)` is injective, which also discharges the `Classical.choose` on
  both sides (via `exists_of_fixed` and `Classical.choose_spec`).

Then `natCard_groupCohomology_two_quotientToInvariants_units` follows from
`natCard_groupCohomology_iso` and `natCard_groupCohomology_res_mulEquiv`.-/

variable {B E : Type} [Field B] [Field E] [Algebra B E] [FiniteDimensional B E] [IsGalois B E]

open CategoryTheory Representation in
/-- A single `Exists`-statement for a fixed vector of the units representation. -/
lemma exists_of_fixed (H : Subgroup (E ≃ₐ[B] E))
    (x : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    ∃ y : (IntermediateField.fixedField H)ˣ,
      x.1 = Additive.ofMul
        (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom y) :=
  (mem_invariants_iff_repr H x.1).mp fun h =>
    (Representation.mem_invariants
      (ρ := (Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) x.1).mp x.2 h

open CategoryTheory Representation in
/-- The fixed vector corresponding to a unit of the fixed field. -/
def fixedOfUnit (H : Subgroup (E ≃ₐ[B] E)) (y : (IntermediateField.fixedField H)ˣ) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) :=
  ⟨Additive.ofMul (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom y),
    (mem_invariants_iff_repr H _).mpr ⟨y, rfl⟩⟩

open CategoryTheory Representation in
/-- **The module identification.**  The `H`-invariants of the units representation of `E/B` are
the units of the fixed field `E^H`. -/
noncomputable def unitsInvEquiv (H : Subgroup (E ≃ₐ[B] E)) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) ≃
      Additive (IntermediateField.fixedField H)ˣ where
  toFun x := Classical.choose (exists_of_fixed H x)
  invFun y := fixedOfUnit H y
  left_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec (exists_of_fixed H x)).symm
  right_inv y := by
    have h := Classical.choose_spec (exists_of_fixed H (fixedOfUnit H y))
    have h2 := congrArg Additive.toMul h
    change (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom) y =
      (Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
        (Classical.choose (exists_of_fixed H (fixedOfUnit H y))) at h2
    exact Units.map_injective (f := (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
      (RingHom.injective _) h2.symm

open CategoryTheory Representation in
/-- Additivity of `unitsInvEquiv`. -/
lemma unitsInvEquiv_map_add (H : Subgroup (E ≃ₐ[B] E))
    (x y : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    unitsInvEquiv H (x + y) = unitsInvEquiv H x + unitsInvEquiv H y := by
  have hx := Classical.choose_spec (exists_of_fixed H x)
  have hy := Classical.choose_spec (exists_of_fixed H y)
  have hxy := Classical.choose_spec (exists_of_fixed H (x + y))
  rw [show unitsInvEquiv H (x + y) = Classical.choose (exists_of_fixed H (x + y)) from rfl,
    show unitsInvEquiv H x = Classical.choose (exists_of_fixed H x) from rfl,
    show unitsInvEquiv H y = Classical.choose (exists_of_fixed H y) from rfl]
  change (Classical.choose (exists_of_fixed H (x + y)) :
      (IntermediateField.fixedField H)ˣ) =
    Classical.choose (exists_of_fixed H x) * Classical.choose (exists_of_fixed H y)
  apply Units.map_injective (f := (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
    (RingHom.injective _)
  simp only [map_mul]
  have key : Additive.ofMul ((Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
        (Classical.choose (exists_of_fixed H (x + y))))
      = Additive.ofMul ((Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
          (Classical.choose (exists_of_fixed H x)))
        + Additive.ofMul ((Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom)
          (Classical.choose (exists_of_fixed H y))) := by
    rw [← hxy, ← hx, ← hy]
    rfl
  have key2 := congrArg Additive.toMul key
  simpa using key2

open CategoryTheory Representation in
/-- The `AddEquiv` underlying the module identification. -/
noncomputable def unitsInvAddEquiv (H : Subgroup (E ≃ₐ[B] E)) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) ≃+
      Additive (IntermediateField.fixedField H)ˣ where
  toFun := unitsInvEquiv H
  invFun := (unitsInvEquiv H).symm
  left_inv := (unitsInvEquiv H).left_inv
  right_inv := (unitsInvEquiv H).right_inv
  map_add' := unitsInvEquiv_map_add H

open CategoryTheory Representation in
/-- **The `ℤ`-linear module identification.** -/
noncomputable def unitsInvLinearEquiv (H : Subgroup (E ≃ₐ[B] E)) :
    Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype) ≃ₗ[ℤ]
      Additive (IntermediateField.fixedField H)ˣ :=
  (unitsInvAddEquiv H).toLinearEquiv fun c x => by
    change unitsInvEquiv H (c • x) = c • unitsInvEquiv H x
    exact AddMonoidHom.map_zsmul (unitsInvAddEquiv H).toAddMonoidHom c x

open CategoryTheory Representation in
/-- `unitsInvLinearEquiv` is the unique unit of the fixed field mapping to a given invariant
unit of `Eˣ`. -/
lemma units_map_unitsInvLinearEquiv (H : Subgroup (E ≃ₐ[B] E))
    (z : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    Units.map (algebraMap (IntermediateField.fixedField H) E).toMonoidHom
        (unitsInvLinearEquiv H z) = Additive.toMul z.1 := by
  have h := Classical.choose_spec (exists_of_fixed H z)
  rw [show unitsInvLinearEquiv H z = Classical.choose (exists_of_fixed H z) from rfl]
  exact (congrArg Additive.toMul h).symm

open CategoryTheory Representation in
/-- `algebraMap B₁ E` commutes with the Galois action, for `B₁ ⊆ E` normal over `B`. -/
lemma units_map_smul_restrictNormal (B₁ : IntermediateField B E) [Normal B ↥B₁]
    (g : E ≃ₐ[B] E) (w : B₁ˣ) :
    Units.map (algebraMap B₁ E).toMonoidHom
        (Units.map (AlgEquiv.restrictNormalHom B₁ g).toRingEquiv.toMonoidHom w)
      = Units.map g.toRingEquiv.toMonoidHom
          (Units.map (algebraMap B₁ E).toMonoidHom w) := by
  apply Units.ext
  simp only [Units.coe_map]
  exact AlgEquiv.restrictNormal_commutes g B₁ (w : ↥B₁)

open CategoryTheory Representation in
lemma unitsInvLinearEquiv_equivariant (H : Subgroup (E ≃ₐ[B] E)) [H.Normal]
    (g : (E ≃ₐ[B] E) ⧸ H)
    (x : Representation.invariants ((Rep.ofAlgebraAutOnUnits B E).ρ.comp H.subtype)) :
    unitsInvLinearEquiv H (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ g x)
      = (Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
          (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))).ρ g
        (unitsInvLinearEquiv H x) := by
  let B₁ := IntermediateField.fixedField H
  haveI : Normal B ↥B₁ := by
    haveI : IsGalois B ↥B₁ := IsGalois.of_fixedField_normal_subgroup H
    infer_instance
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  apply Units.map_injective (f := (algebraMap ↥B₁ E).toMonoidHom) (RingHom.injective _)
  rw [units_map_unitsInvLinearEquiv H
    (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ (QuotientGroup.mk g') x)]
  rw [show (Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits B ↥B₁)).ρ (QuotientGroup.mk g')
      = (Rep.ofAlgebraAutOnUnits B ↥B₁).ρ (AlgEquiv.restrictNormalHom ↥B₁ g') from rfl]
  change Additive.toMul (((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ
        (QuotientGroup.mk g') x).1
      = Units.map (algebraMap ↥B₁ E).toMonoidHom
          (Additive.ofMul (Units.map (AlgEquiv.restrictNormalHom ↥B₁ g').toRingEquiv.toMonoidHom
            (Additive.toMul (unitsInvLinearEquiv H x))))
  rw [show Units.map (algebraMap ↥B₁ E).toMonoidHom
        (Additive.ofMul (Units.map (AlgEquiv.restrictNormalHom ↥B₁ g').toRingEquiv.toMonoidHom
          (Additive.toMul (unitsInvLinearEquiv H x))))
      = Units.map (algebraMap ↥B₁ E).toMonoidHom
          (Units.map (AlgEquiv.restrictNormalHom ↥B₁ g').toRingEquiv.toMonoidHom
            (Additive.toMul (unitsInvLinearEquiv H x))) from rfl]
  rw [show ((((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ
        (QuotientGroup.mk g') x).1) = (Rep.ofAlgebraAutOnUnits B E).ρ g' x.1 from rfl]
  rw [units_map_smul_restrictNormal B₁ g' (Additive.toMul (unitsInvLinearEquiv H x))]
  rw [show Units.map (algebraMap ↥B₁ E).toMonoidHom (Additive.toMul (unitsInvLinearEquiv H x))
      = Units.map (algebraMap ↥B₁ E).toMonoidHom (unitsInvLinearEquiv H x) from rfl]
  rw [units_map_unitsInvLinearEquiv H x]
  rfl

open CategoryTheory Representation in
theorem natCard_groupCohomology_two_quotientToInvariants_units (H : Subgroup (E ≃ₐ[B] E)) [H.Normal] :
    Nat.card (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) =
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) 2) := by
  haveI : Normal B ↥(IntermediateField.fixedField H) := by
    haveI : IsGalois B ↥(IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
    infer_instance
  have hiso : (Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H ≅
      Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) :=
    { hom := Rep.ofHom ⟨(unitsInvLinearEquiv H).toLinearMap, fun g => by
        apply LinearMap.ext; intro x
        exact unitsInvLinearEquiv_equivariant H g x⟩
      inv := Rep.ofHom ⟨(unitsInvLinearEquiv H).symm.toLinearMap, fun g => by
        apply LinearMap.ext; intro y
        show (unitsInvLinearEquiv H).symm
            ((Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
              (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))).ρ g y)
          = ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ g
              ((unitsInvLinearEquiv H).symm y)
        conv_lhs => rw [show y = (unitsInvLinearEquiv H) ((unitsInvLinearEquiv H).symm y) from
          (LinearEquiv.apply_symm_apply (unitsInvLinearEquiv H) y).symm]
        rw [(unitsInvLinearEquiv_equivariant H g ((unitsInvLinearEquiv H).symm y)).symm]
        rw [LinearEquiv.symm_apply_apply]⟩
      hom_inv_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [Rep.hom_comp_toLinearMap]
        simp only [Rep.hom_ofHom, LinearMap.comp_apply]
        exact LinearEquiv.symm_apply_apply (unitsInvLinearEquiv H) x
      inv_hom_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [Rep.hom_comp_toLinearMap]
        simp only [Rep.hom_ofHom, LinearMap.comp_apply]
        exact LinearEquiv.apply_symm_apply (unitsInvLinearEquiv H) x }
  rw [natCard_groupCohomology_iso hiso 2]
  exact natCard_groupCohomology_res_mulEquiv (IsGalois.normalAutEquivQuotient H)
    (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) 2



namespace Commons.NumberTheory.NumberField.Completion

namespace S31


/-! ## Universe-polymorphic transport of the algebra automorphism group -/



section Conj

variable {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀]

/-- Conjugation by the ring isomorphism `eE` transports a `B`-algebra automorphism of `E`
to a `B₀`-algebra automorphism of `E₀`, using that `eE` intertwines the two structure maps
along `eB`. -/
noncomputable def conjAlgEquiv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ : E ≃ₐ[B] E) :
    E₀ ≃ₐ[B₀] E₀ :=
  AlgEquiv.ofRingEquiv (f := eE.symm.trans (σ.toRingEquiv.trans eE)) (by
    intro y
    change eE (σ (eE.symm (algebraMap B₀ E₀ y))) = algebraMap B₀ E₀ y
    have hy : algebraMap B₀ E₀ y = eE (algebraMap B E (eB.symm y)) := by
      rw [h (eB.symm y), eB.apply_symm_apply]
    rw [hy, RingEquiv.symm_apply_apply, AlgEquiv.commutes, h (eB.symm y), eB.apply_symm_apply])

/-- The inverse transport (conjugation by `eE.symm`). -/
noncomputable def conjAlgEquivSymm (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (τ : E₀ ≃ₐ[B₀] E₀) :
    E ≃ₐ[B] E :=
  AlgEquiv.ofRingEquiv (f := eE.trans (τ.toRingEquiv.trans eE.symm)) (by
    intro x
    change eE.symm (τ (eE (algebraMap B E x))) = algebraMap B E x
    rw [h x, AlgEquiv.commutes, ← h x, RingEquiv.symm_apply_apply])

@[simp]
theorem conjAlgEquiv_apply (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ : E ≃ₐ[B] E) (a : E₀) :
    conjAlgEquiv eB eE h σ a = eE (σ (eE.symm a)) := by
  rw [conjAlgEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rfl

@[simp]
theorem conjAlgEquivSymm_apply (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (τ : E₀ ≃ₐ[B₀] E₀) (a : E) :
    conjAlgEquivSymm eB eE h τ a = eE.symm (τ (eE a)) := by
  rw [conjAlgEquivSymm, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rfl

theorem conjAlgEquivSymm_conjAlgEquiv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (σ : E ≃ₐ[B] E) :
    conjAlgEquivSymm eB eE h (conjAlgEquiv eB eE h σ) = σ := by
  apply AlgEquiv.ext
  intro a
  simp only [conjAlgEquivSymm_apply, conjAlgEquiv_apply, RingEquiv.symm_apply_apply]

theorem conjAlgEquiv_conjAlgEquivSymm (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) (τ : E₀ ≃ₐ[B₀] E₀) :
    conjAlgEquiv eB eE h (conjAlgEquivSymm eB eE h τ) = τ := by
  apply AlgEquiv.ext
  intro b
  simp only [conjAlgEquiv_apply, conjAlgEquivSymm_apply, RingEquiv.apply_symm_apply]

/-- Conjugation by a ring isomorphism `eE` that the base change `eB` intertwines yields an
equivalence between the `B`-algebra automorphisms of `E` and the `B₀`-algebra automorphisms
of `E₀`. -/
noncomputable def conjAlgEquivEquiv (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    (E ≃ₐ[B] E) ≃ (E₀ ≃ₐ[B₀] E₀) where
  toFun := conjAlgEquiv eB eE h
  invFun := conjAlgEquivSymm eB eE h
  left_inv := conjAlgEquivSymm_conjAlgEquiv eB eE h
  right_inv := conjAlgEquiv_conjAlgEquivSymm eB eE h

end Conj

theorem natCard_algEquiv_eq_of_ringEquiv_univ {B E B₀ E₀ : Type*} [Field B] [Field E] [Field B₀] [Field E₀]
    [Algebra B E] [Algebra B₀ E₀] (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (E ≃ₐ[B] E) = Nat.card (E₀ ≃ₐ[B₀] E₀) :=
  Nat.card_congr (conjAlgEquivEquiv eB eE h)


/-! ## The two-sided transport of the norm quotient -/

theorem natCard_quotient_units_range_norm_eq_of_ringEquiv_univ {B E B₀ E₀ : Type*} [Field B]
    [Field E] [Field B₀] [Field E₀] [Algebra B E] [Algebra B₀ E₀]
    (eB : B ≃+* B₀) (eE : E ≃+* E₀)
    (h : ∀ x : B, eE (algebraMap B E x) = algebraMap B₀ E₀ (eB x)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (B₀ˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))) := by
  have hnorm : ∀ u : Eˣ,
      Units.map eB.toMulEquiv (Units.map (Algebra.norm B : E →* B) u) =
        Units.map (Algebra.norm B₀ : E₀ →* B₀) (Units.map eE.toMulEquiv u) := by
    intro u
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    show eB (Algebra.norm B (u : E)) = Algebra.norm B₀ (eE (u : E))
    have hh := Algebra.norm_eq_of_equiv_equiv eB eE (RingHom.ext (fun x => (h x).symm)) (u : E)
    rw [hh, RingEquiv.apply_symm_apply]
  have hmap : Subgroup.map (Units.map eB.toMulEquiv)
        (MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨Units.map eE.toMulEquiv u, (hnorm u).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨Units.map (Algebra.norm B : E →* B) (Units.map eE.symm.toMulEquiv v),
        ⟨Units.map eE.symm.toMulEquiv v, rfl⟩, ?_⟩
      rw [hnorm (Units.map eE.symm.toMulEquiv v)]
      congr 1
      ext
      simp
  haveI : (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  haveI : (MonoidHom.range (Units.map (Algebra.norm B₀ : E₀ →* B₀))).Normal :=
    Subgroup.normal_of_isMulCommutative _
  exact Nat.card_congr (QuotientGroup.congr _ _ (Units.mapEquiv eB.toMulEquiv) hmap).toEquiv

/-! ## Small models -/

/-- A `Fintype` is `Small.{0}`. -/
theorem small_of_fintype_univ {α : Type*} [Fintype α] : Small.{0} α :=
  small_of_injective (Fintype.equivFin α).injective

/-- A module that is finitely generated over a `Type 0` ring is `Small.{0}`. -/
theorem small_of_moduleFinite_univ {R M : Type*} [Semiring R] [Small.{0} R] [AddCommMonoid M]
    [Module R M] [Module.Finite R M] : Small.{0} M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have hrange : Set.range (fun x : ↥s => (x : M)) = (↑s : Set M) := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  have hsurj : Function.Surjective (Finsupp.linearCombination R (fun x : ↥s => (x : M))) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hrange, hs]
  haveI : Small.{0} ↥s := small_of_fintype_univ
  haveI : Small.{0} (↥s →₀ R) := inferInstance
  exact small_of_surjective (f := Finsupp.linearCombination R (fun x : ↥s => (x : M))) hsurj

/-- **A number field has a `Type 0` model**, compatibly with a ring isomorphism. -/
theorem exists_typeZero_field_ringEquiv (K : Type*) [Field K] [NumberField K] :
    ∃ (K₀ : Type) (_ : Field K₀), Nonempty (K ≃+* K₀) := by
  obtain ⟨K₀, ⟨e⟩⟩ := (small_iff K).mp (small_of_moduleFinite_univ (R := ℚ) (M := K))
  letI : Field K₀ := Equiv.field e.symm
  exact ⟨K₀, inferInstance, ⟨(Equiv.ringEquiv e.symm).symm⟩⟩


/-! ## The bridge -/

/-- **The universe bridge for the abelian norm index identity at a completion.**

If `|Fˣ ⧸ N_{E/F}(Eˣ)| = |Gal(E/F)|` holds for all `Type 0` data (`h0`), then it holds in
arbitrary universes. -/
theorem natCard_quotient_units_range_norm_eq_card_of_abelian_local_universe_bridge
    (h0 : ∀ {K₀ : Type} [Field K₀] [NumberField K₀]
        (Q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₀))
        {E₀ : Type} [Field E₀] [Algebra (Q₀.adicCompletion K₀) E₀]
        [FiniteDimensional (Q₀.adicCompletion K₀) E₀] [IsGalois (Q₀.adicCompletion K₀) E₀]
        (hcomm : ∀ a b : E₀ ≃ₐ[Q₀.adicCompletion K₀] E₀, a * b = b * a),
        Nat.card ((Q₀.adicCompletion K₀)ˣ ⧸ MonoidHom.range
            (Units.map (Algebra.norm (Q₀.adicCompletion K₀) : E₀ →* Q₀.adicCompletion K₀))) =
          Nat.card (E₀ ≃ₐ[Q₀.adicCompletion K₀] E₀))
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K))) =
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
  classical
  -- (1) a `Type 0` model `K₀` of the number field, with its canonical `ℚ`-algebra structure
  obtain ⟨K₀, hK₀f, ⟨eKr⟩⟩ := exists_typeZero_field_ringEquiv K
  haveI : CharZero K₀ := by
    refine ⟨fun m n hmn => ?_⟩
    have h2 : ((m : K)) = ((n : K)) := by
      have h := congrArg eKr.symm hmn
      simpa using h
    exact Nat.cast_injective h2
  haveI : FiniteDimensional ℚ K₀ :=
    Module.Finite.of_surjective ((eKr.toRatAlgEquiv).toLinearEquiv.toLinearMap)
      (eKr.toRatAlgEquiv).toLinearEquiv.surjective
  haveI : NumberField K₀ := NumberField.mk
  have eK : K ≃ₐ[ℚ] K₀ := eKr.toRatAlgEquiv
  -- (2) transport the completion
  obtain ⟨Q₀, Φ, hΦ⟩ :=
    Commons.NumberTheory.NumberField.completion_ringEquiv_of_algEquiv eK Q
  -- (3) the `F₀`-algebra structure on `E`
  let g : Q₀.adicCompletion K₀ →+* E :=
    (algebraMap (Q.adicCompletion K) E).comp Φ.symm.toRingHom
  letI : Algebra (Q₀.adicCompletion K₀) E := g.toAlgebra
  have hΦc : ∀ x : Q.adicCompletion K, g (Φ x) = algebraMap (Q.adicCompletion K) E x := by
    intro x
    show (algebraMap (Q.adicCompletion K) E) (Φ.symm (Φ x)) = algebraMap (Q.adicCompletion K) E x
    rw [Φ.symm_apply_apply]
  have hcompat : ∀ x : Q.adicCompletion K,
      (RingEquiv.refl E) (algebraMap (Q.adicCompletion K) E x)
        = algebraMap (Q₀.adicCompletion K₀) E (Φ x) := by
    intro x
    show algebraMap (Q.adicCompletion K) E x = g (Φ x)
    rw [hΦc]
  haveI hfdE : FiniteDimensional (Q₀.adicCompletion K₀) E :=
    Commons.Algebra.Module.moduleFinite_of_ringEquiv Φ (RingEquiv.refl E) hcompat
  haveI hgalE : IsGalois (Q₀.adicCompletion K₀) E :=
    Commons.FieldTheory.Galois.isGalois_of_ringEquiv Φ (RingEquiv.refl E) hcompat
  -- (4) a `Type 0` model `E₀` of `E` over `F₀`
  obtain ⟨E₀, hE₀f, hE₀a, hE₀fd, ⟨eE⟩⟩ :=
    exists_type_zero_field_of_finiteDimensional
      (F := Q₀.adicCompletion K₀) (E := E)
  letI : Algebra (Q₀.adicCompletion K₀) E₀ := hE₀a
  letI : FiniteDimensional (Q₀.adicCompletion K₀) E₀ := hE₀fd
  haveI hgalE₀ : IsGalois (Q₀.adicCompletion K₀) E₀ := IsGalois.of_algEquiv eE
  -- (5) the compatibility of the two transports
  have hcomp2 : ∀ x : Q.adicCompletion K,
      eE.toRingEquiv (algebraMap (Q.adicCompletion K) E x)
        = algebraMap (Q₀.adicCompletion K₀) E₀ (Φ x) := by
    intro x
    have h : algebraMap (Q.adicCompletion K) E x = g (Φ x) := (hΦc x).symm
    rw [h]
    show eE (algebraMap (Q₀.adicCompletion K₀) E (Φ x))
      = algebraMap (Q₀.adicCompletion K₀) E₀ (Φ x)
    exact eE.commutes (Φ x)
  -- (6) commutativity transports
  have hconjmul : ∀ (σ τ : E ≃ₐ[Q.adicCompletion K] E),
      conjAlgEquiv Φ eE.toRingEquiv hcomp2 (σ * τ)
        = conjAlgEquiv Φ eE.toRingEquiv hcomp2 σ
          * conjAlgEquiv Φ eE.toRingEquiv hcomp2 τ := by
    intro σ τ
    apply AlgEquiv.ext
    intro a
    simp only [conjAlgEquiv_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]
  have hcomm₀ : ∀ a b : E₀ ≃ₐ[Q₀.adicCompletion K₀] E₀, a * b = b * a := by
    intro a b
    obtain ⟨σ, rfl⟩ := (conjAlgEquivEquiv Φ eE.toRingEquiv hcomp2).surjective a
    obtain ⟨τ, rfl⟩ := (conjAlgEquivEquiv Φ eE.toRingEquiv hcomp2).surjective b
    show conjAlgEquiv Φ eE.toRingEquiv hcomp2 σ * conjAlgEquiv Φ eE.toRingEquiv hcomp2 τ
      = conjAlgEquiv Φ eE.toRingEquiv hcomp2 τ * conjAlgEquiv Φ eE.toRingEquiv hcomp2 σ
    rw [← hconjmul, ← hconjmul, hcomm σ τ]
  -- (7) the `Type 0` statement and the transports back
  have hkey := h0 (K₀ := K₀) Q₀ (E₀ := E₀) hcomm₀
  have hquot : Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K))) =
      Nat.card ((Q₀.adicCompletion K₀)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q₀.adicCompletion K₀) : E₀ →* Q₀.adicCompletion K₀))) :=
    natCard_quotient_units_range_norm_eq_of_ringEquiv_univ
      (B := Q.adicCompletion K) (E := E) (B₀ := Q₀.adicCompletion K₀) (E₀ := E₀)
      Φ eE.toRingEquiv hcomp2
  have hcard : Nat.card (E ≃ₐ[Q.adicCompletion K] E) =
      Nat.card (E₀ ≃ₐ[Q₀.adicCompletion K₀] E₀) :=
    natCard_algEquiv_eq_of_ringEquiv_univ
      (B := Q.adicCompletion K) (E := E) (B₀ := Q₀.adicCompletion K₀) (E₀ := E₀)
      Φ eE.toRingEquiv hcomp2
  rw [hquot, hkey, ← hcard]



open CategoryTheory Representation

set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

/-- **The Tate assembly** (Type 0): a fundamental class of order `#Gal` plus Hilbert 90 and the
cardinalities at all subgroups give the norm index identity. -/
theorem tate_assembly {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a)
    (h1 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1))
    (h2 : ∀ H : Subgroup (E ≃ₐ[B] E),
      Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) =
        Nat.card H)
    (α : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2)
    (hα : addOrderOf α = Nat.card (E ≃ₐ[B] E)) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (E ≃ₐ[B] E) := by
  letI : CommGroup (E ≃ₐ[B] E) := { (inferInstance : Group (E ≃ₐ[B] E)) with mul_comm := hcomm }
  haveI : Group.IsSolvable (E ≃ₐ[B] E) := inferInstance
  have hTate :=
    Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
      (Rep.ofAlgebraAutOnUnits B E) h1 h2 α hα
  have hzero := Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units B E
  have hneg :=
    Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_neg_two_of_commutative
      (E ≃ₐ[B] E) hcomm
  rw [← hzero, ← hTate, hneg]

/-- Any intermediate field of a finite *abelian* Galois extension is Galois over the base. -/
theorem isGalois_intermediateField_aux {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) (M : IntermediateField B E) :
    IsGalois B ↥M := by
  haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
  haveI : (M.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  haveI h : IsGalois B ↥(IntermediateField.fixedField M.fixingSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup M.fixingSubgroup
  exact (IsGalois.fixedField_fixingSubgroup (F := B) (E := E) M) ▸ h

/-- The Galois group of an intermediate field of a finite *abelian* Galois extension is
commutative. -/
theorem commute_intermediateField_aux {B E : Type} [Field B] [Field E] [Algebra B E]
    [FiniteDimensional B E] [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) (M : IntermediateField B E) :
    ∀ a b : ↥M ≃ₐ[B] ↥M, a * b = b * a := by
  haveI : IsMulCommutative (E ≃ₐ[B] E) := IsMulCommutative.of_comm hcomm
  haveI hH : (M.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  let e := IsGalois.normalAutEquivQuotient (K := B) (L := E) M.fixingSubgroup
  have hq : ∀ x y : (E ≃ₐ[B] E) ⧸ M.fixingSubgroup, x * y = y * x := by
    intro x y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x' y']
  have key : ∀ a b : ↥(IntermediateField.fixedField M.fixingSubgroup) ≃ₐ[B]
      ↥(IntermediateField.fixedField M.fixingSubgroup), a * b = b * a := by
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul, hq]
  rw [IsGalois.fixedField_fixingSubgroup (F := B) (E := E) M] at key
  exact key

/-- **The universe-`0` abelian norm index identity at an arbitrary base**, conditional on the
fundamental class. -/
theorem target_univ0
    (hfund : ∀ {K : Type} [Field K] [NumberField K]
      (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      {F E : Type} [Field F] [Field E]
      [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) F E]
      [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
      [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E],
      ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
        addOrderOf α = Module.finrank F E)
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    ∀ (M : IntermediateField B E) (p : ℕ), IsPGroup p (M ≃ₐ[B] M) →
      Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : M →* B))) =
        Nat.card (M ≃ₐ[B] M) := by
  intro M p hp
  haveI hgalM : IsGalois B ↥M := isGalois_intermediateField_aux hcomm M
  have hcommM : ∀ a b : ↥M ≃ₐ[B] ↥M, a * b = b * a := commute_intermediateField_aux hcomm M
  haveI : IsMulCommutative (↥M ≃ₐ[B] ↥M) := IsMulCommutative.of_comm hcommM
  have h1 : ∀ H : Subgroup (↥M ≃ₐ[B] ↥M),
      Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B ↥M)) 1) :=
    fun H => Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units H
  have h2 : ∀ H : Subgroup (↥M ≃ₐ[B] ↥M),
      Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B ↥M)) 2) =
        Nat.card H := by
    intro H
    rw [Commons.NumberTheory.NumberField.Completion.NatCardP9.natCard_groupCohomology_two_res_units H]
    let L : IntermediateField B ↥M := IntermediateField.fixedField H
    have hcommH : ∀ a b : ↥M ≃ₐ[↥L] ↥M, a * b = b * a := by
      have hHcomm : ∀ x y : ↥H, x * y = y * x := fun x y => Subtype.ext (by
        show (x : ↥M ≃ₐ[B] ↥M) * (y : ↥M ≃ₐ[B] ↥M) = (y : ↥M ≃ₐ[B] ↥M) * (x : ↥M ≃ₐ[B] ↥M)
        exact hcommM x y)
      intro a b
      have hH : (IntermediateField.subgroupEquivAlgEquiv H).symm (a * b)
          = (IntermediateField.subgroupEquivAlgEquiv H).symm (b * a) := by
        rw [map_mul, map_mul]
        exact hHcomm _ _
      exact (IntermediateField.subgroupEquivAlgEquiv H).symm.injective hH
    haveI htower : IsScalarTower (Q.adicCompletion K) ↥L ↥M :=
      IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B ↥L x]
        rw [← IsScalarTower.algebraMap_apply B ↥L ↥M]
        exact IsScalarTower.algebraMap_apply (Q.adicCompletion K) B ↥M x
    haveI hfdL : FiniteDimensional (Q.adicCompletion K) ↥L :=
      FiniteDimensional.trans (Q.adicCompletion K) B ↥L
    haveI hfdM : FiniteDimensional (Q.adicCompletion K) ↥M :=
      FiniteDimensional.trans (Q.adicCompletion K) B ↥M
    have hle := Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
      (Q := Q) (B := ↥L) (E := ↥M) hcommH
    have hge := Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank
      (Q := Q) (F := ↥L) (E := ↥M)
    rw [le_antisymm hle hge, ← IsGalois.card_aut_eq_finrank ↥L ↥M]
    exact Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv H).symm.toEquiv
  haveI hfdMtop : FiniteDimensional (Q.adicCompletion K) ↥M :=
    FiniteDimensional.trans (Q.adicCompletion K) B ↥M
  obtain ⟨α, hα⟩ := hfund (Q := Q) (F := B) (E := ↥M)
  rw [← IsGalois.card_aut_eq_finrank B ↥M] at hα
  exact tate_assembly hcommM h1 h2 α hα




/-- **The `Type 0` abelian norm index identity at a completion**, conditional on the fundamental
class. -/
theorem base_univ0
    (hfund : ∀ {K : Type} [Field K] [NumberField K]
      (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      {F E : Type} [Field F] [Field E]
      [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) F E]
      [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
      [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E],
      ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
        addOrderOf α = Module.finrank F E)
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K))) =
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
  classical
  have hp : IsPGroup 0 (↥(⊤ : IntermediateField (Q.adicCompletion K) E) ≃ₐ[Q.adicCompletion K]
      ↥(⊤ : IntermediateField (Q.adicCompletion K) E)) := by
    intro g
    exact ⟨1, by simp⟩
  have h := target_univ0 hfund (B := Q.adicCompletion K) (E := E) Q hcomm ⊤ 0 hp
  have hcomp : ∀ x : Q.adicCompletion K,
      (IntermediateField.topEquiv (F := Q.adicCompletion K) (E := E)).toRingEquiv
          (algebraMap (Q.adicCompletion K)
            ↥(⊤ : IntermediateField (Q.adicCompletion K) E) x)
        = algebraMap (Q.adicCompletion K) E x := by
    intro x
    exact (IntermediateField.topEquiv (F := Q.adicCompletion K) (E := E)).commutes x
  have hquot := natCard_quotient_units_range_norm_eq_of_ringEquiv_univ
    (RingEquiv.refl (Q.adicCompletion K))
    (IntermediateField.topEquiv (F := Q.adicCompletion K) (E := E)).toRingEquiv hcomp
  have hcard := natCard_algEquiv_eq_of_ringEquiv_univ
    (B := Q.adicCompletion K) (E := ↥(⊤ : IntermediateField (Q.adicCompletion K) E))
    (B₀ := Q.adicCompletion K) (E₀ := E)
    (RingEquiv.refl (Q.adicCompletion K))
    (IntermediateField.topEquiv (F := Q.adicCompletion K) (E := E)).toRingEquiv hcomp
  rw [← hquot, h, hcard]

/-- **The abelian local norm index identity in arbitrary universes**, conditional on the
fundamental class. -/
theorem abelian_local_of_fund
    (hfund : ∀ {K : Type} [Field K] [NumberField K]
      (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      {F E : Type} [Field F] [Field E]
      [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) F E]
      [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
      [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E],
      ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
        addOrderOf α = Module.finrank F E)
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.range
        (Units.map (Algebra.norm (Q.adicCompletion K) : E →* Q.adicCompletion K))) =
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) :=
  natCard_quotient_units_range_norm_eq_card_of_abelian_local_universe_bridge
    (base_univ0 hfund) Q hcomm

end S31

/-! ## The local Galois group of `q | Q` is abelian when `Gal(L/K)` is

The group `Gal(L_q / K_Q)` is the decomposition subgroup `D_q ≤ Gal(L/K)` (a *subgroup* of an
abelian group), via `decompositionSubgroupMulEquivLocalGalois`. -/
set_option backward.isDefEq.respectTransparency false in
theorem localCommute_of_commute {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, a * b = b * a := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    adicCompletionAlgebra Q q hq
  intro a b
  obtain ⟨x, rfl⟩ :=
    (decompositionSubgroupMulEquivLocalGalois
      Q q hq).surjective a
  obtain ⟨y, rfl⟩ :=
    (decompositionSubgroupMulEquivLocalGalois
      Q q hq).surjective b
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (hcomm ↑x ↑y))

theorem natCard_quotient_units_range_norm_adicCompletion_of_commute {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  have hindex : Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))) =
      Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    natCard_quotient_units_range_norm_eq_card_of_abelian_local Q
      (localCommute_of_commute Q q hq hcomm)
  have hcard : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_finrank
      Q q hq
  rw [hindex, hcard]


end Commons.NumberTheory.NumberField.Completion
