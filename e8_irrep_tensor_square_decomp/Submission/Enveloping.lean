import ChallengeDeps
import Mathlib.Order.Atoms

open LeanEval.RepresentationTheory
open scoped TensorProduct

noncomputable section

namespace Submission.Enveloping

open UniversalEnvelopingAlgebra

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The enveloping algebra of a Lie algebra is generated (as an `R`-algebra) by the image of
the canonical map `ι : L → U(𝔩)`. -/
theorem uea_adjoin_range_ι :
    Algebra.adjoin R (Set.range (ι R : L → UniversalEnvelopingAlgebra R L)) = ⊤ := by
  apply le_antisymm
  · intro u hu; trivial
  · intro u hu
    rcases (RingCon.mkₐ_surjective (α := R) (ringCon R L)) u with ⟨t, rfl⟩
    have ht : t ∈ (Algebra.adjoin R (Set.range (TensorAlgebra.ι R (M := L))) : Set (TensorAlgebra R L)) := by
      simp [TensorAlgebra.adjoin_range_ι]
    have hmm : (mkAlgHom R L) t ∈
        (Algebra.adjoin R (Set.range (TensorAlgebra.ι R (M := L)))).map (mkAlgHom R L) := by
      exact Subalgebra.mem_map.mpr ⟨t, ht, rfl⟩
    rw [AlgHom.map_adjoin] at hmm
    have hfunext : (mkAlgHom R L) ∘ (TensorAlgebra.ι R (M := L)) =
        (ι R : L → UniversalEnvelopingAlgebra R L) := by
      ext x; rfl
    have hrange : (mkAlgHom R L) '' (Set.range (TensorAlgebra.ι R (M := L))) =
        Set.range (ι R : L → UniversalEnvelopingAlgebra R L) := by
      rw [← Set.range_comp, hfunext]
    rw [hrange] at hmm
    exact hmm

/-- The action of `ι x` in the module transported to the enveloping algebra is the original
Lie action of `x`. -/
@[simp] theorem ι_smul_eq_lie (x : L) (m : M) : (ι R x) • m = ⁅x, m⁆ := by
  change (lift R (LieModule.toEnd R L M) (ι R x)) m = ⁅x, m⁆
  rw [lift_ι_apply]
  rfl

/-- Scalars of the base ring act as usual. -/
@[simp] theorem algebraMap_smul_eq_smul (r : R) (m : M) :
    (algebraMap R (UniversalEnvelopingAlgebra R L) r) • m = r • m := by
  change (lift R (LieModule.toEnd R L M) (algebraMap R (UniversalEnvelopingAlgebra R L) r)) m = r • m
  simp

/-- Multiplication in the enveloping algebra acts as composition. -/
@[simp] theorem mul_smul_eq_smul_smul (u v : UniversalEnvelopingAlgebra R L) (m : M) :
    (u * v) • m = u • (v • m) := by
  change (lift R (LieModule.toEnd R L M) (u * v)) m =
    (lift R (LieModule.toEnd R L M) u) ((lift R (LieModule.toEnd R L M) v) m)
  simp

/-- Addition in the enveloping algebra acts additively. -/
@[simp] theorem add_smul_eq_add (u v : UniversalEnvelopingAlgebra R L) (m : M) :
    (u + v) • m = u • m + v • m := by
  change (lift R (LieModule.toEnd R L M) (u + v)) m =
    (lift R (LieModule.toEnd R L M) u) m + (lift R (LieModule.toEnd R L M) v) m
  simp

/-- Lie submodules are stable under the action of the enveloping algebra. -/
theorem enveloping_smul_mem_of_lieSubmodule (N : LieSubmodule R L M)
    (u : UniversalEnvelopingAlgebra R L) {m : M} (hm : m ∈ N) : u • m ∈ N := by
  let p : (x : UniversalEnvelopingAlgebra R L) →
      x ∈ Algebra.adjoin R (Set.range (ι R : L → UniversalEnvelopingAlgebra R L)) → Prop :=
    fun x _ => ∀ ⦃m : M⦄, m ∈ N → x • m ∈ N
  have hu : u ∈ Algebra.adjoin R (Set.range (ι R : L → UniversalEnvelopingAlgebra R L)) := by
    rw [uea_adjoin_range_ι]; trivial
  have hmain : ∀ ⦃m : M⦄, m ∈ N → u • m ∈ N := by
    change p u hu
    refine Algebra.adjoin_induction (p := p) ?_ ?_ ?_ ?_ hu
    · intro x hx m hm
      rcases hx with ⟨a, rfl⟩
      change (mkAlgHom R L (TensorAlgebra.ι R a)) • m ∈ N
      have hsmul : (mkAlgHom R L (TensorAlgebra.ι R a)) • m = ⁅a, m⁆ := by
        simpa using (ι_smul_eq_lie a m)
      rw [hsmul]
      exact N.lie_mem (x := a) hm
    · intro r _m hm
      simpa using N.smul_mem' r hm
    · intro x y hx hy hpx hpy m hm
      simpa [add_smul_eq_add] using N.add_mem (hpx hm) (hpy hm)
    · intro x y hx hy hpx hpy m hm
      simpa [mul_smul_eq_smul_smul] using hpx (hpy hm)
  exact hmain hm

/-- A Lie submodule is stable under the action of the enveloping algebra, and hence can be
viewed as a submodule of `M` over `U(𝔩)`. -/
def toEnveloping (N : LieSubmodule R L M) : Submodule (UniversalEnvelopingAlgebra R L) M where
  carrier := N.carrier
  zero_mem' := N.zero_mem'
  add_mem' := N.add_mem'
  smul_mem' := fun u {_m} hm => enveloping_smul_mem_of_lieSubmodule N u hm

/-- Conversely, a submodule of `M` over `U(𝔩)`, pulled back along `ι : 𝔩 → U(𝔩)`, is a Lie
submodule. -/
def ofEnveloping (W : Submodule (UniversalEnvelopingAlgebra R L) M) : LieSubmodule R L M where
  carrier := W.carrier
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := fun r {m} hm => by
    simpa [algebraMap_smul_eq_smul] using (W.smul_mem' (algebraMap R (UniversalEnvelopingAlgebra R L) r) hm)
  lie_mem := fun x {m} hm => by
    have hsmul : (ι R x) • m = ⁅x, m⁆ := ι_smul_eq_lie x m
    rw [← hsmul]
    exact W.smul_mem' (ι R x) hm

@[simp] theorem mem_toEnveloping (N : LieSubmodule R L M) (m : M) :
    m ∈ toEnveloping N ↔ m ∈ N := Iff.rfl

@[simp] theorem mem_ofEnveloping (W : Submodule (UniversalEnvelopingAlgebra R L) M) (m : M) :
    m ∈ ofEnveloping W ↔ m ∈ W := Iff.rfl

theorem ofEnveloping_comp_toEnveloping (N : LieSubmodule R L M) :
    ofEnveloping (toEnveloping N) = N := by
  ext m
  simp

theorem toEnveloping_comp_ofEnveloping (W : Submodule (UniversalEnvelopingAlgebra R L) M) :
    toEnveloping (ofEnveloping W) = W := by
  ext m
  simp

/-- The order isomorphism between Lie submodules and submodules over the enveloping algebra,
under the canonical module structure on a Lie module. -/
def lieModuleSubmoduleEquiv : LieSubmodule R L M ≃o Submodule (UniversalEnvelopingAlgebra R L) M where
  toFun := toEnveloping
  invFun := ofEnveloping
  left_inv := ofEnveloping_comp_toEnveloping
  right_inv := toEnveloping_comp_ofEnveloping
  map_rel_iff' := by
    intro N₁ N₂
    constructor
    · intro h m hm
      simpa using h (by simpa using hm)
    · intro h m hm
      simpa using h (by simpa using hm)

/-- A Lie module is irreducible iff it is simple as a module over its enveloping algebra. -/
theorem isIrreducible_iff_isSimpleModule :
    LieModule.IsIrreducible R L M ↔ IsSimpleModule (UniversalEnvelopingAlgebra R L) M := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff (lieModuleSubmoduleEquiv)

end Submission.Enveloping
