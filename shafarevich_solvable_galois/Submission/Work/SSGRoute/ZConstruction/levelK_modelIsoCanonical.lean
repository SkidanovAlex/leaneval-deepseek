import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupH1locLcHoms
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical model identification `V_A ≅ lcHoms p ↥(decomp (k := ↥K) A)`

The gate `Work.SSGRoute.ZConstruction.levelK_pairing_productFormula` consumes a family of forms
indexed by the *subgroup* `H = decomp k A ⊓ K.fixingSubgroup`, while the canonical local Tate
pairing is naturally attached to a *place* `A`.  For the transport between two places with the same
local group the model identification must be canonical: the `Classical.choose` of
`mupH1locLcHoms` is not, because two places resolve their `∃`-statements independently.

This file puts the *explicit* identification `mupH1locChar` (a `def`, determined by the computation
rule `mupH1locChar (toClass a) = mupCocycleChar ⟨a, _⟩`) in that role and proves the four
properties that the pairing consumes:

* `levelKModelIsoCanon_zero` — it sends `0` to `1`;
* `levelKModelIsoCanon_add` — it is additive;
* `levelKModelIsoCanon_eq_one_iff` — its kernel is trivial (so it is injective);
* `levelKModelIsoCanon_bijective` — it is bijective.

Additivity and surjectivity use only the two computation rules of `mupH1locChar` together with
`toClass_surjective`/`toClass_add` and `exists_cocycle_of_lcHoms`; no arithmetic input is needed.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

/-- **The canonical model identification**: the explicit character map `mupH1locChar`, in the role
of the model identification `V_A ≅ ↥(lcHoms p ↥(decomp (k := ↥K) A))`. -/
abbrev levelKModelIsoCanon :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  Work.SSGRoute.ZDataMup.mupH1locChar (p := p) (k := k) (Ω := Ω) (K := K) A

/-- The canonical model identification kills `0`. -/
theorem levelKModelIsoCanon_zero :
    levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) 0 = 1 := by
  have h0 : (0 : (Ω ≃ₐ[k] Ω) → ZMod p) ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := Submodule.zero_mem _
  have h1 : Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (0 : (Ω ≃ₐ[k] Ω) → ZMod p) = 0 := by
    rw [Work.SSGRoute.toClass, dif_pos h0]
    exact map_zero _
  show Work.SSGRoute.ZDataMup.mupH1locChar (p := p) (k := k) (Ω := Ω) (K := K) A 0 = 1
  rw [← h1, Work.SSGRoute.ZDataMup.mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K)
    A _ h0]
  exact Work.SSGRoute.ZDataMup.mupCocycleChar_zero (p := p) (k := k) (Ω := Ω) (K := K) A

/-- The canonical model identification is additive. -/
theorem levelKModelIsoCanon_add
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) (x + y) =
      levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) x *
        levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) y := by
  obtain ⟨a, ha, rfl⟩ := Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
    (SSGRoute.decomp k A ⊓ K.fixingSubgroup) x
  obtain ⟨b, hb, rfl⟩ := Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
    (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y
  rw [← Work.SSGRoute.toClass_add p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ha hb]
  simp only [levelKModelIsoCanon,
    Work.SSGRoute.ZDataMup.mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A _ ha,
    Work.SSGRoute.ZDataMup.mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A _ hb,
    Work.SSGRoute.ZDataMup.mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A _
      (add_mem ha hb)]
  exact Work.SSGRoute.ZDataMup.mupCocycleChar_add (p := p) (k := k) (Ω := Ω) (K := K) A
    ⟨a, ha⟩ ⟨b, hb⟩

/-- **The kernel of the canonical model identification is trivial.**  A class whose character is
trivial has a representative vanishing on the local group, hence is a coboundary. -/
theorem levelKModelIsoCanon_eq_one_iff
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) x
    rw [show levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) =
        Work.SSGRoute.ZDataMup.mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A ⟨a, ha⟩
        from Work.SSGRoute.ZDataMup.mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K)
          A a ha] at hx
    have hvan : ∀ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, a g = 0 := by
      intro g hg
      have h2 := congrArg (fun χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) =>
        (χ.1 : ↥(SSGRoute.decomp (k := ↥K) A) → Multiplicative (ZMod p))
          (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩)) hx
      rw [Work.SSGRoute.ZDataMup.mupCocycleChar_spec (p := p) (k := k) (Ω := Ω) (K := K) A
        ⟨a, ha⟩ ⟨g, hg⟩] at h2
      have h2' : Multiplicative.ofAdd (a g) = 1 := by simpa using h2
      exact Multiplicative.ofAdd.injective h2'
    rw [Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ha, Work.SSGRoute.mem_coboundaries]
    refine ⟨0, fun g hg => ?_⟩
    have hres : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (E := K)]
      exact hg.2
    rw [hvan g hg, hres, one_smul, sub_self]
  · rintro rfl
    exact levelKModelIsoCanon_zero (p := p) (k := k) (Ω := Ω) (K := K) (A := A)

/-- **The canonical model identification is injective.** -/
theorem levelKModelIsoCanon_injective :
    Function.Injective (levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A)) := by
  have hneg : ∀ u : Work.SSGRoute.H1loc p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) (-u) =
        (levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A) u)⁻¹ := by
    intro u
    have h := levelKModelIsoCanon_add (p := p) (k := k) (Ω := Ω) (K := K) (A := A) (-u) u
    rw [neg_add_cancel, levelKModelIsoCanon_zero] at h
    exact (mul_eq_one_iff_eq_inv).mp h.symm
  intro x y hxy
  refine eq_of_sub_eq_zero ?_
  rw [sub_eq_add_neg]
  refine (levelKModelIsoCanon_eq_one_iff (p := p) (k := k) (Ω := Ω) (K := K) (A := A)
    (x + -y)).mp ?_
  rw [levelKModelIsoCanon_add, hneg, hxy, mul_inv_cancel]

/-- **The canonical model identification is surjective**: every locally constant character of the
level-`K` local group is the character of a cocycle (`exists_cocycle_of_lcHoms`). -/
theorem levelKModelIsoCanon_surjective :
    Function.Surjective (levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A)) := by
  intro χ
  obtain ⟨a, ha, hval⟩ := Work.SSGRoute.ZDataMup.exists_cocycle_of_lcHoms (p := p) (k := k)
    (Ω := Ω) (K := K) A χ
  refine ⟨Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a, ?_⟩
  rw [show levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A)
      (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) =
      Work.SSGRoute.ZDataMup.mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A ⟨a, ha⟩
      from Work.SSGRoute.ZDataMup.mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K)
        A a ha]
  refine Subtype.ext (MonoidHom.ext fun y => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective y
  rw [Work.SSGRoute.ZDataMup.mupCocycleChar_spec (p := p) (k := k) (Ω := Ω) (K := K) A
    ⟨a, ha⟩ g]
  exact (hval g).symm

/-- **The canonical model identification is bijective.** -/
theorem levelKModelIsoCanon_bijective :
    Function.Bijective (levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A)) :=
  ⟨levelKModelIsoCanon_injective (p := p) (k := k) (Ω := Ω) (K := K) (A := A),
    levelKModelIsoCanon_surjective (p := p) (k := k) (Ω := Ω) (K := K) (A := A)⟩

end

end Work.SSGRoute.ZConstruction
