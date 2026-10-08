import Mathlib
import Submission.Work.PSTAB.UnipotentSL2
import Submission.Work.PSTAB.QuadPairIrr
import Submission.OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible
import Submission.OddOrder.GroupTheory.RepresentationTheory.BaseChange

set_option autoImplicit false
set_option linter.style.haveILetI false

-- Allow the compiler to see through the `Field`/`Ring`/`Semiring` instance towers on the
-- self-intertwiner ring `Representation.IntertwiningMap ρ ρ`, as in
-- `Submission/OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean`.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace Work.PSTAB

/-- A submodule which is invariant under the group action is `⊥` or `⊤` when `ρ` is
irreducible.  This is the "unbundled" form of `Representation.IsIrreducible` used by
`Work.PSTAB.UnipotentSL2` and `OddOrder.BG.AppA.quadratic_two_generated_irreducible_finrank_eq_two`. -/
lemma eq_bot_or_eq_top_of_isIrreducible {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) [ρ.IsIrreducible] :
    ∀ W : Submodule F V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let W' : Subrepresentation ρ := { toSubmodule := W, apply_mem_toSubmodule := hW }
  rcases eq_bot_or_eq_top W' with h | h
  · left
    change W' = (⊥ : Subrepresentation ρ) at h
    exact congrArg Subrepresentation.toSubmodule h
  · right
    change W' = (⊤ : Subrepresentation ρ) at h
    exact congrArg Subrepresentation.toSubmodule h

/-- The quadratic condition `(ρ g - 1)^2 = 0` survives regarding `ρ` over its self-intertwiner
field (`OddOrder.RepresentationTheory.overEnd`). -/
lemma overEnd_sub_one_sq {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (g : G)
    (h : ((ρ g : Module.End F V) - 1) ^ 2 = 0) :
    (((OddOrder.RepresentationTheory.overEnd ρ) g :
        Module.End (Representation.IntertwiningMap ρ ρ) V) - 1) ^ 2 = 0 := by
  set A : Module.End (Representation.IntertwiningMap ρ ρ) V :=
    (OddOrder.RepresentationTheory.overEnd ρ) g with hA
  have key : ∀ w : V, (A - 1) w = ((ρ g : Module.End F V) - 1) w := by
    intro w
    rw [hA]
    simp [LinearMap.sub_apply, Module.End.one_apply]
  ext v
  rw [pow_two, Module.End.mul_apply, key, key]
  have hh : ((ρ g : Module.End F V) - 1) (((ρ g : Module.End F V) - 1) v) = 0 := by
    have h2 := congrArg (fun f : Module.End F V => f v) h
    simp only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] at h2
    exact h2
  exact hh

/-- The quadratic condition `(A - 1)^2 = 0` survives scalar extension. -/
lemma baseChange_sub_one_sq {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]
    {V : Type*} [AddCommGroup V] [Module K V] (A : Module.End K V)
    (hA : (A - 1) ^ 2 = 0) :
    ((LinearMap.baseChange E A - 1 : Module.End E (TensorProduct K E V))) ^ 2 = 0 := by
  have h1 : (1 : Module.End E (TensorProduct K E V))
      = LinearMap.baseChange E (1 : Module.End K V) :=
    (LinearMap.baseChange_one K V).symm
  rw [h1, ← LinearMap.baseChange_sub, pow_two, ← LinearMap.baseChange_mul, ← pow_two, hA,
    LinearMap.baseChange_zero]

/-- **The quadratic-pair lemma for an absolutely irreducible representation.**  If `ρ` is a
finite-dimensional faithful irreducible representation of a finite group `H` over a field `K`,
`ρ` is *absolutely* irreducible, and `H = ⟨x, y⟩` with `x`, `y` acting as nontrivial unipotents,
then `H` contains a non-cyclic `2`-subgroup with a unique involution.

The proof base-changes `ρ` to an algebraically closed extension `E ⧸ K` (irreducibility is
`habs E`, faithfulness is `baseChangeRepresentation_faithful`), transports the quadratic
conditions, applies BG Appendix A (`quadratic_two_generated_irreducible_finrank_eq_two`) to get
`finrank E = 2`, and concludes with `Work.PSTAB.UnipotentSL2`. -/
theorem quadPair_of_absolutely_irreducible {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [CharP K p]
    {E : Type*} [Field E] [Algebra K E] [IsAlgClosed E] [CharP E p]
    {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K H V) [ρ.IsIrreducible] (hρ : Function.Injective ρ)
    (habs : OddOrder.RepresentationTheory.IsAbsolutelyIrreducible ρ)
    (x y : H) (hgen : Subgroup.closure ({x, y} : Set H) = ⊤)
    (hx : ((ρ x : Module.End K V) - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End K V) - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    ∃ Q : Subgroup H, IsPGroup 2 Q ∧ ¬ IsCyclic Q ∧ ∃! z : Q, orderOf z = 2 := by
  classical
  haveI : Module.FaithfullyFlat K E := inferInstance
  haveI : (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ).IsIrreducible :=
    OddOrder.RepresentationTheory.IsAbsolutelyIrreducible.baseChangeRepresentation_isIrreducible habs E
  have hσfaith : Function.Injective (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) :=
    OddOrder.RepresentationTheory.baseChangeRepresentation_faithful E ρ hρ
  haveI : Nontrivial (TensorProduct K E V) :=
    OddOrder.RepresentationTheory.nontrivial_of_isIrreducible
      (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ)
  have hirrσ := eq_bot_or_eq_top_of_isIrreducible
    (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ)
  have hxσ : (((OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) x :
      Module.End E (TensorProduct K E V)) - 1) ^ 2 = 0 := by
    rw [OddOrder.RepresentationTheory.baseChangeRepresentation_eq_baseChange E ρ x]
    exact baseChange_sub_one_sq _ hx
  have hyσ : (((OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) y :
      Module.End E (TensorProduct K E V)) - 1) ^ 2 = 0 := by
    rw [OddOrder.RepresentationTheory.baseChangeRepresentation_eq_baseChange E ρ y]
    exact baseChange_sub_one_sq _ hy
  have hσxne : (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) x ≠ 1 := by
    intro h
    have hx1 : x = 1 := hσfaith (by rw [h, map_one])
    exact hxne (by rw [hx1, map_one])
  have hσyne : (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) y ≠ 1 := by
    intro h
    have hy1 : y = 1 := hσfaith (by rw [h, map_one])
    exact hyne (by rw [hy1, map_one])
  have hdim : Module.finrank E (TensorProduct K E V) = 2 :=
    OddOrder.BG.AppA.quadratic_two_generated_irreducible_finrank_eq_two
      (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) hσfaith hirrσ
      x y hgen hxσ hσxne hyσ hσyne
  exact Work.PSTAB.UnipotentSL2 hp2 hdim
    (OddOrder.RepresentationTheory.baseChangeRepresentation E ρ) hσfaith hirrσ
    x y hxσ hσxne hyσ hσyne hgen

/-- Route (all ingredients exist in the workspace):
* `K := Representation.IntertwiningMap ρ ρ` is a finite field (`littleWedderburn` + the instances in
  `Submission/OddOrder/GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean`), and
  `Over.End ρ := Representation.overEnd ρ : Representation K H V` is irreducible
  (`Representation.overEnd`), faithful (`overEnd ρ g = ρ g`), and *absolutely* irreducible
  (`OddOrder.RepresentationTheory.isAbsolutelyIrreducible_overEnd`).
* Put `E := AlgebraicClosure K` and `σ := OddOrder.RepresentationTheory.baseChangeRepresentation E (overEnd ρ)`.
  Then `σ` is irreducible (`IsAbsolutelyIrreducible.baseChangeRepresentation_isIrreducible`),
  faithful (`baseChangeRepresentation_faithful`, `Module.FaithfullyFlat K E`), and the quadratic
  conditions transport along base change (`LinearMap.baseChange_mul/sub/one/zero`, via
  `baseChangeRepresentation_eq_baseChange`); `σ x ≠ 1` follows from `hρ` and `hxne`.
* `OddOrder.BG.AppA.quadratic_two_generated_irreducible_finrank_eq_two` gives `finrank E = 2`.
* `Work.PSTAB.UnipotentSL2` (same `E`, `H`, base-changed `V`, `u := x`, `v := y`, `hgen`) gives the
  bad subgroup `Q ≤ H`.
`CharP K p` comes from `F`-algebra structure (`charP_of_injective_algebraMap`), `CharP E p` from the
`AlgebraicClosure` instance. -/
theorem QuadPairBadSubgroup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {F : Type*} [Field F] [CharP F p] [Finite F]
    {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (ρ : Representation F H V) [ρ.IsIrreducible] (hρ : Function.Injective ρ)
    (x y : H) (hgen : Subgroup.closure ({x, y} : Set H) = ⊤)
    (hx : ((ρ x : Module.End F V) - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End F V) - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    ∃ Q : Subgroup H, IsPGroup 2 Q ∧ ¬ IsCyclic Q ∧ ∃! z : Q, orderOf z = 2 := by
  classical
  -- `K = Hom_FH(V, V)` is a finite field (the `Field`/`Finite` instances are global).
  haveI : CharP (Representation.IntertwiningMap ρ ρ) p :=
    charP_of_injective_algebraMap
      (RingHom.injective (algebraMap F (Representation.IntertwiningMap ρ ρ))) p
  haveI : FiniteDimensional (Representation.IntertwiningMap ρ ρ) V :=
    Module.Finite.of_restrictScalars_finite F (Representation.IntertwiningMap ρ ρ) V
  -- `ρ` regarded over `K` is (absolutely) irreducible and faithful.
  have hOverInj : Function.Injective (OddOrder.RepresentationTheory.overEnd ρ) := by
    intro g h hgh
    apply hρ
    ext v
    exact congrArg
      (fun f : Module.End (Representation.IntertwiningMap ρ ρ) V => f v) hgh
  have habs : OddOrder.RepresentationTheory.IsAbsolutelyIrreducible
      (OddOrder.RepresentationTheory.overEnd ρ) :=
    OddOrder.RepresentationTheory.isAbsolutelyIrreducible_overEnd (ρ := ρ)
  -- The quadratic conditions transported to `overEnd ρ`.
  have hx' : (((OddOrder.RepresentationTheory.overEnd ρ) x :
      Module.End (Representation.IntertwiningMap ρ ρ) V) - 1) ^ 2 = 0 :=
    overEnd_sub_one_sq ρ x hx
  have hy' : (((OddOrder.RepresentationTheory.overEnd ρ) y :
      Module.End (Representation.IntertwiningMap ρ ρ) V) - 1) ^ 2 = 0 :=
    overEnd_sub_one_sq ρ y hy
  have hxne' : (OddOrder.RepresentationTheory.overEnd ρ) x ≠ 1 := by
    intro h
    exact hxne (by
      ext v
      exact congrArg
        (fun f : Module.End (Representation.IntertwiningMap ρ ρ) V => f v) h)
  have hyne' : (OddOrder.RepresentationTheory.overEnd ρ) y ≠ 1 := by
    intro h
    exact hyne (by
      ext v
      exact congrArg
        (fun f : Module.End (Representation.IntertwiningMap ρ ρ) V => f v) h)
  exact quadPair_of_absolutely_irreducible hp2
    (K := Representation.IntertwiningMap ρ ρ)
    (E := AlgebraicClosure (Representation.IntertwiningMap ρ ρ))
    (ρ := OddOrder.RepresentationTheory.overEnd ρ) hOverInj habs
    x y hgen hx' hxne' hy' hyne'

end Work.PSTAB
