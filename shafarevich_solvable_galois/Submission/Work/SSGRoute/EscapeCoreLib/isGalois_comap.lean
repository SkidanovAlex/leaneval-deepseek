import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Galois-ness of a field restricted to a subfield

If `L` is an intermediate field containing `M` and `M / k` is Galois, then the copy of `M` inside
`L` (the `comap` of `M` along the inclusion `L → Ω`) is Galois over `k`.  This is the "restriction
into a finite Galois `L`" step of the escape construction: it lets the fields `M`, `N` of the
Čebotarev step be viewed inside `L`, where the Galois correspondence works.

Mathlib has no instance or lemma for `IsGalois` of a `comap` (`Normal.tower_bot_of_normal`,
`IsGalois.tower_bot` do not exist under those names), so the field isomorphism `↥M ≃ₐ[k] ↥(M.comap f)`
is built by hand and `IsGalois.of_algEquiv` is applied.

The `↥K`-variant is stated with `L` given as an `IntermediateField ↥K Ω` — that is the shape in
which the ambient contains the base, so that `Algebra ↥K ↥L` is an instance and the inclusion
`IsScalarTower.toAlgHom ↥K ↥L Ω` is available without any `letI` in the statement.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.SSGRoute.EscapeCoreLib

/-- **`M` restricted to a containing field `L` is Galois over `k`.** -/
theorem isGalois_comap_of_le {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (L : IntermediateField k Ω) (M : IntermediateField k Ω) [IsGalois k M] (hML : M ≤ L) :
    IsGalois k ↥(M.comap (IsScalarTower.toAlgHom k ↥L Ω)) := by
  let f : ↥L →ₐ[k] Ω := IsScalarTower.toAlgHom k ↥L Ω
  let φ : ↥M →ₐ[k] ↥(M.comap f) :=
    { toFun := fun y => ⟨⟨(y : Ω), hML y.2⟩, y.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl
      commutes' := fun r => Subtype.ext rfl }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      refine Subtype.ext ?_
      have h2 : ((φ a : ↥(M.comap f)) : ↥L) = ((φ b : ↥(M.comap f)) : ↥L) :=
        congrArg Subtype.val hab
      have h3 := congrArg Subtype.val h2
      simpa [φ] using h3
    · intro x
      refine ⟨⟨(x : ↥L), x.2⟩, ?_⟩
      exact Subtype.ext (Subtype.ext rfl)
  exact IsGalois.of_algEquiv (AlgEquiv.ofBijective φ hφ)

/-- **The identification `↥M ≃ₐ[↥K] ↥(M.comap f)` of a field `M ≤ L` with its copy inside `L`.**

The map is `y ↦ ⟨⟨(y : Ω), hML y.2⟩, y.2⟩`; it is bijective because `M ≤ L`, so every element of
`M` is of the form `f ⟨x, hx⟩` with `x ∈ L`. -/
noncomputable def comapAlgEquiv {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (L : IntermediateField ↥K Ω)
    (M : IntermediateField ↥K Ω) (hML : M ≤ L) :
    ↥M ≃ₐ[↥K] ↥(M.comap (IsScalarTower.toAlgHom ↥K ↥L Ω)) := by
  let f : ↥L →ₐ[↥K] Ω := IsScalarTower.toAlgHom ↥K ↥L Ω
  let φ : ↥M →ₐ[↥K] ↥(M.comap f) :=
    { toFun := fun y => ⟨⟨(y : Ω), hML y.2⟩, y.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl
      commutes' := fun r => Subtype.ext rfl }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      refine Subtype.ext ?_
      have h2 : ((φ a : ↥(M.comap f)) : ↥L) = ((φ b : ↥(M.comap f)) : ↥L) :=
        congrArg Subtype.val hab
      have h3 := congrArg Subtype.val h2
      simpa [φ] using h3
    · intro x
      exact ⟨⟨(x : ↥L), x.2⟩, Subtype.ext (Subtype.ext rfl)⟩
  exact AlgEquiv.ofBijective φ hφ

/-- The underlying element in `Ω` is unchanged by `comapAlgEquiv`. -/
@[simp] theorem comapAlgEquiv_coe {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (L : IntermediateField ↥K Ω)
    (M : IntermediateField ↥K Ω) (hML : M ≤ L) (y : ↥M) :
    ((comapAlgEquiv K L M hML y : ↥(M.comap (IsScalarTower.toAlgHom ↥K ↥L Ω))) : Ω) = (y : Ω) :=
  rfl

/-- **The `↥K`-variant**: `M / ↥K` Galois, restricted to a containing `↥K`-field `L`. -/
theorem isGalois_comap_of_le_over
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω)
    (L : IntermediateField ↥K Ω)
    (M : IntermediateField ↥K Ω) [IsGalois ↥K M] (hML : M ≤ L) :
    IsGalois ↥K ↥(M.comap (IsScalarTower.toAlgHom ↥K ↥L Ω)) :=
  IsGalois.of_algEquiv (comapAlgEquiv K L M hML)

/-- **Transport of an automorphism of `M` fixing `M ⊓ N` to the copy of `M` inside `L`.**

If `α : ↥M ≃ₐ[↥K] ↥M` fixes pointwise the elements of `M` that lie in `N`, then the conjugate
`e⁻¹ ∘ α ∘ e` along `comapAlgEquiv` fixes pointwise the elements of the copy of `M` inside `L`
that lie in the copy of `N`.  This is what lets the extension lemma
`exists_algEquiv_restrict_eq_of_fixing` be applied inside `L` with the `hαfix` hypothesis of the
unrestricted statement. -/
theorem comapAlgEquiv_transport {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (L : IntermediateField ↥K Ω)
    (M N : IntermediateField ↥K Ω) (hML : M ≤ L)
    (α : ↥M ≃ₐ[↥K] ↥M)
    (hαfix : ∀ y : ↥M, ((y : Ω) ∈ N) → ((α y : ↥M) : Ω) = (y : Ω)) :
    ∀ x : ↥(M.comap (IsScalarTower.toAlgHom ↥K ↥L Ω)),
      (x : Ω) ∈ N →
      ((((comapAlgEquiv K L M hML).symm.trans
        (α.trans (comapAlgEquiv K L M hML))) x :
          ↥(M.comap (IsScalarTower.toAlgHom ↥K ↥L Ω))) : Ω) = (x : Ω) := by
  intro x hx
  set e := comapAlgEquiv K L M hML with he
  have h1 : ((e.symm x : ↥M) : Ω) = (x : Ω) := by
    have h := comapAlgEquiv_coe K L M hML (e.symm x)
    simp only [he, AlgEquiv.apply_symm_apply] at h
    exact h.symm
  have h2 := hαfix (e.symm x) (by rw [h1]; exact hx)
  change (((α.trans e) (e.symm x) : ↥(M.comap (IsScalarTower.toAlgHom ↥K ↥L Ω))) : Ω) = (x : Ω)
  rw [AlgEquiv.trans_apply, comapAlgEquiv_coe]
  rw [h2, h1]

end Work.SSGRoute.EscapeCoreLib
