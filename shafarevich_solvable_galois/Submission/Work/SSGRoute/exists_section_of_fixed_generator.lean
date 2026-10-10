import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Submission.Work.SSGRoute.phi1_mono_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ## Auxiliary: morphisms out of the trivial `ZMod p`-module

The coefficient ring `Coeff = ULift ℤ` carries the generic instance `ULift.module`, which shadows
the honest `Module Coeff Y` structure `Y.hV2` of a general `Y : Rep Coeff G` and makes
`Rep.ofHom`-based morphisms into `Y` ill-elaborated.  We disable that instance in the next section
and re-provide the (legitimate) `Coeff`-module structure on `ZMod p` explicitly.  (Same device as
in `Submission/Work/SSGRoute/phi1_mono_base.lean`.) -/

section ZModTrivialExt

attribute [-instance] ULift.module

local instance zmodModuleCoeffHere (n : ℕ) : Module Coeff (ZMod n) := ULift.module

/-- A morphism out of the trivial `Coeff`-module `ZMod p` is determined by its value at `1`:
`ZMod p` is generated as an abelian group (a fortiori as a `Coeff`-module) by `1`, so two additive
maps agreeing at `1` agree everywhere. -/
theorem hom_trivial_zmod_eq_of_apply_one (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    {Y : Rep Coeff G} (f g : Rep.trivial Coeff G (ZMod p) ⟶ Y) (h : f 1 = g 1) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [show ((n : ℤ) : ZMod p) = n • (1 : ZMod p) from (Int.smul_one_eq_cast n).symm]
  rw [map_zsmul, map_zsmul]
  exact congrArg (fun z : Y => n • z) h

end ZModTrivialExt

/-! ## The main lemma -/

/-- **A fixed element mapping to a generator gives a splitting.** Let `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0`
be a short complex of `D`-modules with `S.X₂` killed by a prime `p`, and let `e : S.X₃ ≅ 𝔽_p` be a
`D`-module isomorphism onto the trivial module. If `m ∈ S.X₂` is `D`-fixed and `e (S.g m) = 1`, then
`S.g : S.X₂ ⟶ S.X₃` admits a section in `Rep Coeff D`. -/
theorem exists_section_of_fixed_generator (p : ℕ) [Fact p.Prime] {D : Type} [Group D]
    (S : ShortComplex (Rep Coeff D))
    (e : S.X₃ ≅ Rep.trivial Coeff D (ZMod p))
    (hp : ∀ m : S.X₂, p • m = 0)
    (m : S.X₂) (hmD : ∀ δ : D, S.X₂.ρ δ m = m)
    (hm : e.hom (S.g m) = 1) :
    ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  -- `S.g m` is the element of `S.X₃` corresponding to `1 ∈ 𝔽_p`
  have hgm : S.g m = e.inv (1 : ZMod p) := by
    rw [← hm]
    exact (Rep.inv_hom_apply _ _ e (S.g m)).symm
  -- hence `m ≠ 0`
  have hm0 : m ≠ 0 := by
    intro h
    have h1 : (1 : ZMod p) = 0 := by
      rw [← hm, h]
      simp
    exact one_ne_zero h1
  -- the `D`-equivariant map `𝔽_p → S.X₂` sending `1 ↦ m`
  obtain ⟨t, _, ht_one⟩ := exists_fixed_vector_morphism p S.X₂ m hmD hm0 hp
  -- it is a section of `S.g` after identifying `S.X₃` with `𝔽_p` via `e`
  have ht : t ≫ S.g = e.inv :=
    hom_trivial_zmod_eq_of_apply_one p _ _ (by rw [Rep.comp_apply, ht_one, hgm])
  exact ⟨e.hom ≫ t, by rw [Category.assoc, ht, e.hom_inv_id]⟩

-- self-check: the statement elaborates exactly as requested, with the ambient instances
example (p : ℕ) [Fact p.Prime] {D : Type} [Group D]
    (S : ShortComplex (Rep Coeff D))
    (e : S.X₃ ≅ Rep.trivial Coeff D (ZMod p))
    (hp : ∀ m : S.X₂, p • m = 0)
    (m : S.X₂) (hmD : ∀ δ : D, S.X₂.ρ δ m = m)
    (hm : e.hom (S.g m) = 1) :
    ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ :=
  exists_section_of_fixed_generator p S e hp m hmD hm

end Work.SSGRoute
