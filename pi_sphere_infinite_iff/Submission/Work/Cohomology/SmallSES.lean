import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SmallChains

/-!
# The Mayer–Vietoris short exact sequence of small chains

Let `X` be a topological space and `U`, `V ⊆ X` subsets.  The **Mayer–Vietoris short exact
sequence** of chain complexes is

`0 → C_*(U ∩ V) → C_*(U) ⊕ C_*(V) → C^{U,V}_*(X) → 0`,

where the middle map is `(a, b) ↦ a - b` (the two chains viewed in `X`), and the last term is the
small chain complex of `Submission/Work/Cohomology/SmallChains.lean`.  Exactness at the right uses
that every simplex is small (its image lies in `U` or in `V`); exactness in the middle uses that a
chain supported both in `U` and in `V` is a chain in `U ∩ V`.

Combined with the small-chains theorem (`H_*(C^{U,V}_*(X)) ≅ H_*(X)`) this yields the
Mayer–Vietoris long exact sequence.

## Main definitions

* `inclUVU`, `inclUVV` — the inclusions `U ∩ V ↪ U`, `U ∩ V ↪ V`;
* `smallOfU`, `smallOfV` — the chain maps `C_*(U) ⟶ C^{U,V}_*(X)`, `C_*(V) ⟶ C^{U,V}_*(X)`
  induced by the inclusions `U ↪ X`, `V ↪ X`;
* `mvLeft`, `mvRight` — the two maps of the Mayer–Vietoris sequence.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The inclusion `U ∩ V ↪ U`. -/
def inclUVU (U V : Set X) : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion `U ∩ V ↪ V`. -/
def inclUVV (U V : Set X) : TopCat.of ↥(U ∩ V) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion `U ↪ X`. -/
def inclUX (U : Set X) : TopCat.of U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `V ↪ X`. -/
def inclVX (V : Set X) : TopCat.of V ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Every simplex in the image of `U ↪ X` is small for the pair `(U, V)`. -/
theorem range_inclUX_le (U V : Set X) :
    Subfunctor.range (TopCat.toSSet.map (inclUX U)) ≤ smallSubcomplex U V := by
  intro n x hx
  rw [Subfunctor.range_obj] at hx
  simp only [Set.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  left
  rintro z ⟨w, rfl⟩
  change TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (inclUX U)).app n y) w ∈ U
  rw [toSSetObjEquiv_map_apply]
  exact (TopCat.toSSetObjEquivT (TopCat.of U) n y w).2

/-- The simplicial map `Simp(U) ⟶ small(U,V)` induced by the inclusion of `U` in `X`. -/
def smallLiftU (U V : Set X) : TopCat.toSSet.obj (TopCat.of U) ⟶ smallSSet U V :=
  (smallSubcomplex U V).lift (TopCat.toSSet.map (inclUX U)) (range_inclUX_le U V)

/-- **The chain map `C_*(U) → C^{U,V}_*(X)`** induced by the inclusion `U ↪ X`. -/
def smallOfU (U V : Set X) : singularChains ℤ (TopCat.of U) ⟶ smallChains U V :=
  SSet.chainComplexMap (smallLiftU U V) (ModuleCat.of ℤ ℤ)

/-- Every simplex in the image of `V ↪ X` is small for the pair `(U, V)`. -/
theorem range_inclVX_le (U V : Set X) :
    Subfunctor.range (TopCat.toSSet.map (inclVX V)) ≤ smallSubcomplex U V := by
  intro n x hx
  rw [Subfunctor.range_obj] at hx
  simp only [Set.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  right
  rintro z ⟨w, rfl⟩
  change TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (inclVX V)).app n y) w ∈ V
  rw [toSSetObjEquiv_map_apply]
  exact (TopCat.toSSetObjEquivT (TopCat.of V) n y w).2

/-- The simplicial map `Simp(V) ⟶ small(U,V)` induced by the inclusion of `V` in `X`. -/
def smallLiftV (U V : Set X) : TopCat.toSSet.obj (TopCat.of V) ⟶ smallSSet U V :=
  (smallSubcomplex U V).lift (TopCat.toSSet.map (inclVX V)) (range_inclVX_le U V)

/-- **The chain map `C_*(V) → C^{U,V}_*(X)`** induced by the inclusion `V ↪ X`. -/
def smallOfV (U V : Set X) : singularChains ℤ (TopCat.of V) ⟶ smallChains U V :=
  SSet.chainComplexMap (smallLiftV U V) (ModuleCat.of ℤ ℤ)

/-- The first map of the Mayer–Vietoris sequence:
`C_*(U ∩ V) → C_*(U) ⊕ C_*(V)`, `z ↦ (z, z)`. -/
def mvLeft (U V : Set X) : singularChains ℤ (TopCat.of ↥(U ∩ V)) ⟶
    (singularChains ℤ (TopCat.of U)) ⊞ (singularChains ℤ (TopCat.of V)) :=
  biprod.lift (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ))
    (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ))

/-- The second map of the Mayer–Vietoris sequence:
`C_*(U) ⊕ C_*(V) → C^{U,V}_*(X)`, `(a, b) ↦ a - b`. -/
def mvRight (U V : Set X) :
    (singularChains ℤ (TopCat.of U)) ⊞ (singularChains ℤ (TopCat.of V)) ⟶ smallChains U V :=
  biprod.desc (smallOfU U V) (-(smallOfV U V))

end

end Work.Cohomology
