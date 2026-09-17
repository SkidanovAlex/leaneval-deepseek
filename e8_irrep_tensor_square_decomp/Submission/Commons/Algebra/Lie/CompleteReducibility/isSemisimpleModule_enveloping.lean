import Mathlib
import Submission.Commons.Algebra.Lie.CompleteReducibility.isCompl_of_isKilling

namespace Commons.Algebra.Lie.CompleteReducibility

open UniversalEnvelopingAlgebra

/-!
# Complete reducibility over the universal enveloping algebra

This file proves that a finite-dimensional module `M` over a Lie algebra `L` with non-degenerate
Killing form is a semisimple module over the universal enveloping algebra `U(L)`, where the
`U(L)`-action is transported from the Lie action along the universal property of `U(L)`
(`Module.compHom M (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L M)).toRingHom`).

The key point is the dictionary between Lie submodules of `M` and `U(L)`-submodules of `M`:
they have the same underlying additive subgroups (`toEnveloping` / `ofEnveloping`), and these two
operations are mutually inverse and order-preserving.  Weyl's theorem
(`isCompl_of_isKilling`) gives a Lie-submodule complement of every Lie submodule, which is then
automatically also a `U(L)`-submodule complement.  Hence the lattice of `U(L)`-submodules is
complemented, i.e. `M` is semisimple over `U(L)`.
-/

section Enveloping

variable {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

noncomputable local instance instModuleEnveloping : Module (UniversalEnvelopingAlgebra K L) M :=
  Module.compHom M (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L M)).toRingHom

/-- The enveloping algebra of a Lie algebra is generated (as an `K`-algebra) by the image of
the canonical map `ι : L → U(𝔩)`. -/
theorem uea_adjoin_range_ι :
    Algebra.adjoin K (Set.range (ι K : L → UniversalEnvelopingAlgebra K L)) = ⊤ := by
  apply le_antisymm
  · intro u hu; trivial
  · intro u hu
    rcases (RingCon.mkₐ_surjective (α := K) (ringCon K L)) u with ⟨t, rfl⟩
    have ht : t ∈ (Algebra.adjoin K (Set.range (TensorAlgebra.ι K (M := L))) : Set (TensorAlgebra K L)) := by
      simp [TensorAlgebra.adjoin_range_ι]
    have hmm : (mkAlgHom K L) t ∈
        (Algebra.adjoin K (Set.range (TensorAlgebra.ι K (M := L)))).map (mkAlgHom K L) := by
      exact Subalgebra.mem_map.mpr ⟨t, ht, rfl⟩
    rw [AlgHom.map_adjoin] at hmm
    have hfunext : (mkAlgHom K L) ∘ (TensorAlgebra.ι K (M := L)) =
        (ι K : L → UniversalEnvelopingAlgebra K L) := by
      ext x; rfl
    have hrange : (mkAlgHom K L) '' (Set.range (TensorAlgebra.ι K (M := L))) =
        Set.range (ι K : L → UniversalEnvelopingAlgebra K L) := by
      rw [← Set.range_comp, hfunext]
    rw [hrange] at hmm
    exact hmm

/-- The action of `ι x` in the module transported to the enveloping algebra is the original
Lie action of `x`. -/
@[simp] theorem ι_smul_eq_lie (x : L) (m : M) : (ι K x) • m = ⁅x, m⁆ := by
  change (lift K (LieModule.toEnd K L M) (ι K x)) m = ⁅x, m⁆
  rw [lift_ι_apply]
  rfl

/-- Scalars of the base ring act as usual. -/
@[simp] theorem algebraMap_smul_eq_smul (r : K) (m : M) :
    (algebraMap K (UniversalEnvelopingAlgebra K L) r) • m = r • m := by
  change (lift K (LieModule.toEnd K L M) (algebraMap K (UniversalEnvelopingAlgebra K L) r)) m = r • m
  simp

/-- Multiplication in the enveloping algebra acts as composition. -/
@[simp] theorem mul_smul_eq_smul_smul (u v : UniversalEnvelopingAlgebra K L) (m : M) :
    (u * v) • m = u • (v • m) := by
  change (lift K (LieModule.toEnd K L M) (u * v)) m =
    (lift K (LieModule.toEnd K L M) u) ((lift K (LieModule.toEnd K L M) v) m)
  simp

/-- Addition in the enveloping algebra acts additively. -/
@[simp] theorem add_smul_eq_add (u v : UniversalEnvelopingAlgebra K L) (m : M) :
    (u + v) • m = u • m + v • m := by
  change (lift K (LieModule.toEnd K L M) (u + v)) m =
    (lift K (LieModule.toEnd K L M) u) m + (lift K (LieModule.toEnd K L M) v) m
  simp

/-- Lie submodules are stable under the action of the enveloping algebra. -/
theorem enveloping_smul_mem_of_lieSubmodule (N : LieSubmodule K L M)
    (u : UniversalEnvelopingAlgebra K L) {m : M} (hm : m ∈ N) : u • m ∈ N := by
  let p : (x : UniversalEnvelopingAlgebra K L) →
      x ∈ Algebra.adjoin K (Set.range (ι K : L → UniversalEnvelopingAlgebra K L)) → Prop :=
    fun x _ => ∀ ⦃m : M⦄, m ∈ N → x • m ∈ N
  have hu : u ∈ Algebra.adjoin K (Set.range (ι K : L → UniversalEnvelopingAlgebra K L)) := by
    rw [uea_adjoin_range_ι]; trivial
  have hmain : ∀ ⦃m : M⦄, m ∈ N → u • m ∈ N := by
    change p u hu
    refine Algebra.adjoin_induction (p := p) ?_ ?_ ?_ ?_ hu
    · intro x hx m hm
      rcases hx with ⟨a, rfl⟩
      change (mkAlgHom K L (TensorAlgebra.ι K a)) • m ∈ N
      have hsmul : (mkAlgHom K L (TensorAlgebra.ι K a)) • m = ⁅a, m⁆ := by
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
def toEnveloping (N : LieSubmodule K L M) : Submodule (UniversalEnvelopingAlgebra K L) M where
  carrier := N.carrier
  zero_mem' := N.zero_mem'
  add_mem' := N.add_mem'
  smul_mem' := fun u {_m} hm => enveloping_smul_mem_of_lieSubmodule N u hm

/-- Conversely, a submodule of `M` over `U(𝔩)`, pulled back along `ι : 𝔩 → U(𝔩)`, is a Lie
submodule. -/
def ofEnveloping (W : Submodule (UniversalEnvelopingAlgebra K L) M) : LieSubmodule K L M where
  carrier := W.carrier
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := fun r {m} hm => by
    simpa [algebraMap_smul_eq_smul] using (W.smul_mem' (algebraMap K (UniversalEnvelopingAlgebra K L) r) hm)
  lie_mem := fun x {m} hm => by
    have hsmul : (ι K x) • m = ⁅x, m⁆ := ι_smul_eq_lie x m
    rw [← hsmul]
    exact W.smul_mem' (ι K x) hm

@[simp] theorem mem_toEnveloping (N : LieSubmodule K L M) (m : M) :
    m ∈ toEnveloping N ↔ m ∈ N := Iff.rfl

@[simp] theorem mem_ofEnveloping (W : Submodule (UniversalEnvelopingAlgebra K L) M) (m : M) :
    m ∈ ofEnveloping W ↔ m ∈ W := Iff.rfl

theorem ofEnveloping_comp_toEnveloping (N : LieSubmodule K L M) :
    ofEnveloping (toEnveloping N) = N := by
  ext m
  simp

theorem toEnveloping_comp_ofEnveloping (W : Submodule (UniversalEnvelopingAlgebra K L) M) :
    toEnveloping (ofEnveloping W) = W := by
  ext m
  simp

/-- The order isomorphism between Lie submodules and submodules over the enveloping algebra,
under the canonical module structure on a Lie module. -/
def lieModuleSubmoduleEquiv : LieSubmodule K L M ≃o Submodule (UniversalEnvelopingAlgebra K L) M where
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

end Enveloping

theorem isSemisimpleModule_enveloping {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [LieAlgebra.IsKilling K L] [Module.Finite K M] :
    letI : Module (UniversalEnvelopingAlgebra K L) M :=
      Module.compHom M (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L M)).toRingHom
    IsSemisimpleModule (UniversalEnvelopingAlgebra K L) M := by
  letI : Module (UniversalEnvelopingAlgebra K L) M :=
    Module.compHom M (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L M)).toRingHom
  rw [isSemisimpleModule_iff]
  refine ⟨fun W => ?_⟩
  obtain ⟨N', hN'⟩ := isCompl_of_isKilling (ofEnveloping (K := K) (L := L) (M := M) W)
  refine ⟨toEnveloping (K := K) (L := L) (M := M) N', ?_⟩
  have hmap := (lieModuleSubmoduleEquiv (K := K) (L := L) (M := M)).isCompl hN'
  simpa [lieModuleSubmoduleEquiv, toEnveloping_comp_ofEnveloping] using hmap

end Commons.Algebra.Lie.CompleteReducibility
