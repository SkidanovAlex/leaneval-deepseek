import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.OpenSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fibre of the reduction map on continuous characters is finite

Let `G` be a topological group and `S` a *commutative* group (no topology on `S`): a
homomorphism `χ : G →* S` is "continuous" exactly when its kernel is open in `G`,
so the set of such `χ` is the set of continuous characters of `G` with values in `S`.

`N ≤ S` a subgroup, `χ₀ : G →* S` an "open kernel" character whose mod `N` reduction is fixed.
The lemma `Work.SSGRoute.fiber_finite_of_quotient` states that the fibre of the reduction
map `χ ↦ (S ⧸ N) ∘ χ` over `χ₀` is finite, provided that the set of `N`-valued characters
with open kernel is finite.

The mathematics is the following.  If `χ` lies in the fibre, put `δ := χ * χ₀⁻¹`
(pointwise: `δ g = χ g * (χ₀ g)⁻¹`), which is an `N`-valued homomorphism because `χ` and
`χ₀` agree modulo `N` (here commutativity of `S` is used: the pointwise quotient of
homomorphisms into an abelian group is again a homomorphism).  The map `χ ↦ δ` is
injective, since `χ = δ * χ₀` recovers `χ` from `δ`.  Finally `ker δ ⊇ ker χ ⊓ ker χ₀`,
which is open because both are, so `δ` has open kernel, i.e. `δ` lies in the finite set.
Hence the fibre embeds into a finite set.
-/

namespace Work.SSGRoute

/-- If `χ` and `χ₀` agree modulo the subgroup `N`, the pointwise quotient `χ * χ₀⁻¹`
takes all its values in `N`. -/
lemma mul_inv_mem_of_comp_eq {G : Type*} [Group G] {S : Type*} [CommGroup S]
    (N : Subgroup S) {χ χ₀ : G →* S}
    (h : (QuotientGroup.mk' N).comp χ = (QuotientGroup.mk' N).comp χ₀) :
    ∀ g : G, (χ * χ₀⁻¹) g ∈ N := by
  intro g
  have hg : (QuotientGroup.mk' N) (χ g) = (QuotientGroup.mk' N) (χ₀ g) := DFunLike.congr_fun h g
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  show (QuotientGroup.mk' N) ((χ * χ₀⁻¹) g) = 1
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, hg, mul_inv_cancel]

/-- If `χ` and `χ₀` are "continuous" (open kernel) then so is the `N`-valued difference
`χ * χ₀⁻¹` restricted to `N`: its kernel contains `ker χ ⊓ ker χ₀`. -/
lemma isOpen_ker_codRestrict_mul_inv {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {S : Type*} [CommGroup S] (N : Subgroup S) {χ χ₀ : G →* S}
    (h : ∀ g : G, (χ * χ₀⁻¹) g ∈ N)
    (hχ : IsOpen (χ.ker : Set G)) (hχ₀ : IsOpen (χ₀.ker : Set G)) :
    IsOpen (((χ * χ₀⁻¹).codRestrict N h).ker : Set G) := by
  rw [MonoidHom.ker_codRestrict]
  refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ χ₀.ker) ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply]
    simp [MonoidHom.mem_ker.mp hx.1, MonoidHom.mem_ker.mp hx.2]
  · exact hχ.inter hχ₀

theorem fiber_finite_of_quotient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {S : Type*} [CommGroup S] (N : Subgroup S) (χ₀ : G →* S)
    (hχ₀ : IsOpen (χ₀.ker : Set G))
    (hNfin : Finite {δ : G →* N // IsOpen (δ.ker : Set G)}) :
    Finite {χ : G →* S // IsOpen (χ.ker : Set G) ∧
      (QuotientGroup.mk' N).comp χ = (QuotientGroup.mk' N).comp χ₀} := by
  classical
  refine @Finite.of_injective _
    {δ : G →* N // IsOpen (δ.ker : Set G)} hNfin
    (fun χ : {χ : G →* S // IsOpen (χ.ker : Set G) ∧
        (QuotientGroup.mk' N).comp χ = (QuotientGroup.mk' N).comp χ₀} =>
      ⟨(χ.1 * χ₀⁻¹).codRestrict N (mul_inv_mem_of_comp_eq N χ.2.2),
        isOpen_ker_codRestrict_mul_inv N (mul_inv_mem_of_comp_eq N χ.2.2) χ.2.1 hχ₀⟩) ?_
  intro χ₁ χ₂ h
  -- the `N`-valued differences coincide, hence so do `χ₁` and `χ₂`
  have hΔ : (χ₁.1 * χ₀⁻¹).codRestrict N (mul_inv_mem_of_comp_eq N χ₁.2.2) =
      (χ₂.1 * χ₀⁻¹).codRestrict N (mul_inv_mem_of_comp_eq N χ₂.2.2) :=
    congrArg Subtype.val h
  have key : ∀ (χ : G →* S) (h : ∀ g : G, (χ * χ₀⁻¹) g ∈ N),
      (N.subtype.comp ((χ * χ₀⁻¹).codRestrict N h)) = χ * χ₀⁻¹ := by
    intro χ h
    ext g
    simp [MonoidHom.codRestrict_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
  have heq : χ₁.1 * χ₀⁻¹ = χ₂.1 * χ₀⁻¹ := by
    calc χ₁.1 * χ₀⁻¹
        = N.subtype.comp ((χ₁.1 * χ₀⁻¹).codRestrict N (mul_inv_mem_of_comp_eq N χ₁.2.2)) :=
          (key χ₁.1 (mul_inv_mem_of_comp_eq N χ₁.2.2)).symm
      _ = N.subtype.comp ((χ₂.1 * χ₀⁻¹).codRestrict N (mul_inv_mem_of_comp_eq N χ₂.2.2)) := by
          rw [hΔ]
      _ = χ₂.1 * χ₀⁻¹ := key χ₂.1 (mul_inv_mem_of_comp_eq N χ₂.2.2)
  refine Subtype.ext (MonoidHom.ext fun g => ?_)
  have hg1 : ((χ₁.1 * χ₀⁻¹) * χ₀) g = χ₁.1 g := by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
    group
  have hg2 : ((χ₂.1 * χ₀⁻¹) * χ₀) g = χ₂.1 g := by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
    group
  rw [← hg1, ← hg2, heq]

end Work.SSGRoute
