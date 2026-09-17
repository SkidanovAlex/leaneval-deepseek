import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.UniversalEnveloping

noncomputable section

namespace Commons.RepresentationTheory.LieEnveloping

open UniversalEnvelopingAlgebra

/-- The enveloping algebra of a Lie algebra is generated as an `R`-algebra by the image of the
canonical map `ι : L → U(L)`. -/
private theorem uea_adjoin_range_ι {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] :
    Algebra.adjoin R
        (Set.range (UniversalEnvelopingAlgebra.ι R :
          L → UniversalEnvelopingAlgebra R L)) = ⊤ := by
  apply le_antisymm
  · intro u hu; trivial
  · intro u hu
    rcases (RingCon.mkₐ_surjective (α := R) (ringCon R L)) u with ⟨t, rfl⟩
    have ht : t ∈ (Algebra.adjoin R
        (Set.range (TensorAlgebra.ι R (M := L))) : Set (TensorAlgebra R L)) := by
      simp [TensorAlgebra.adjoin_range_ι]
    have hmm : (mkAlgHom R L) t ∈
        (Algebra.adjoin R (Set.range (TensorAlgebra.ι R (M := L)))).map (mkAlgHom R L) :=
      Subalgebra.mem_map.mpr ⟨t, ht, rfl⟩
    rw [AlgHom.map_adjoin] at hmm
    have hfunext : (mkAlgHom R L) ∘ (TensorAlgebra.ι R (M := L)) =
        (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L) := by
      ext x; rfl
    have hrange : (mkAlgHom R L) '' (Set.range (TensorAlgebra.ι R (M := L))) =
        Set.range (UniversalEnvelopingAlgebra.ι R :
          L → UniversalEnvelopingAlgebra R L) := by
      rw [← Set.range_comp, hfunext]
    rw [hrange] at hmm
    exact hmm

/-- Scalars of the base ring act as usual on a module over the enveloping algebra compatible
with the `R`-module structure. -/
private theorem algebraMap_smul_eq_smul {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M] (r : R) (m : M) :
    (algebraMap R (UniversalEnvelopingAlgebra R L) r) • m = r • m := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

/-- Lie submodules are stable under the action of the enveloping algebra, when the action of the
`ι`-images is the Lie action. -/
private theorem enveloping_smul_mem_of_lieSubmodule {R L M : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (N : LieSubmodule R L M) (u : UniversalEnvelopingAlgebra R L) {m : M} (hm : m ∈ N) :
    u • m ∈ N := by
  let p : (x : UniversalEnvelopingAlgebra R L) →
      x ∈ Algebra.adjoin R (Set.range (UniversalEnvelopingAlgebra.ι R :
        L → UniversalEnvelopingAlgebra R L)) → Prop :=
    fun x _ => ∀ ⦃m : M⦄, m ∈ N → x • m ∈ N
  have hu : u ∈ Algebra.adjoin R (Set.range (UniversalEnvelopingAlgebra.ι R :
      L → UniversalEnvelopingAlgebra R L)) := by
    rw [uea_adjoin_range_ι]; trivial
  have hmain : ∀ ⦃m : M⦄, m ∈ N → u • m ∈ N := by
    change p u hu
    refine Algebra.adjoin_induction (p := p) ?_ ?_ ?_ ?_ hu
    · intro x hx m hm
      rcases hx with ⟨a, rfl⟩
      rw [hι a m]
      exact N.lie_mem (x := a) hm
    · intro r m hm
      rw [algebraMap_smul_eq_smul r m]
      exact N.smul_mem' r hm
    · intro x y hx hy hpx hpy m hm
      rw [add_smul]
      exact N.add_mem (hpx hm) (hpy hm)
    · intro x y hx hy hpx hpy m hm
      rw [mul_smul]
      exact hpx (hpy hm)
  exact hmain hm

/-- A Lie submodule is stable under the action of the enveloping algebra, and hence can be
viewed as a submodule of `M` over `U(L)`. -/
private def toEnveloping {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (N : LieSubmodule R L M) : Submodule (UniversalEnvelopingAlgebra R L) M where
  carrier := N.carrier
  zero_mem' := N.zero_mem'
  add_mem' := N.add_mem'
  smul_mem' := fun u {_m} hm => enveloping_smul_mem_of_lieSubmodule hι N u hm

/-- Conversely, a submodule of `M` over `U(L)`, pulled back along `ι : L → U(L)`, is a Lie
submodule. -/
private def ofEnveloping {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (W : Submodule (UniversalEnvelopingAlgebra R L) M) : LieSubmodule R L M where
  carrier := W.carrier
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := fun r {m} hm => by
    have h := W.smul_mem' (algebraMap R (UniversalEnvelopingAlgebra R L) r) hm
    rwa [algebraMap_smul_eq_smul r m] at h
  lie_mem := fun x {m} hm => by
    rw [← hι x m]
    exact W.smul_mem' (UniversalEnvelopingAlgebra.ι R x) hm

@[simp] private theorem mem_toEnveloping {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (N : LieSubmodule R L M) (m : M) : m ∈ toEnveloping hι N ↔ m ∈ N := Iff.rfl

@[simp] private theorem mem_ofEnveloping {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (W : Submodule (UniversalEnvelopingAlgebra R L) M) (m : M) :
    m ∈ ofEnveloping hι W ↔ m ∈ W := Iff.rfl

private theorem ofEnveloping_comp_toEnveloping {R L M : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (N : LieSubmodule R L M) : ofEnveloping hι (toEnveloping hι N) = N := by
  ext m
  simp

private theorem toEnveloping_comp_ofEnveloping {R L M : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆)
    (W : Submodule (UniversalEnvelopingAlgebra R L) M) :
    toEnveloping hι (ofEnveloping hι W) = W := by
  ext m
  simp

/-- The order isomorphism between Lie submodules and submodules over the enveloping algebra,
under a module structure whose action on the `ι`-images is the Lie action. -/
private def lieModuleSubmoduleEquiv {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆) :
    LieSubmodule R L M ≃o Submodule (UniversalEnvelopingAlgebra R L) M where
  toFun := toEnveloping hι
  invFun := ofEnveloping hι
  left_inv := ofEnveloping_comp_toEnveloping hι
  right_inv := toEnveloping_comp_ofEnveloping hι
  map_rel_iff' := by
    intro N₁ N₂
    constructor
    · intro h m hm
      simpa using h (by simpa using hm)
    · intro h m hm
      simpa using h (by simpa using hm)

/-- The Lie-module / enveloping-module dictionary, "irreducible = simple".

`M` carries both a Lie-module structure of `L` and a compatible `U(L)`-module structure whose
action on the `ι`-images is the Lie action.  Then `M` is irreducible as a Lie module of `L` if and
only if it is simple as a module over `U(L)`.

(Proof sketch: `LieSubmodule R L M ≃o Submodule (U(L)) M` is an order isomorphism — the forward
map is the identity on the carrier using that Lie submodules are `U(L)`-stable, the backward map
pulls back along `ι` — and `LieModule.IsIrreducible` is `IsSimpleOrder (LieSubmodule R L M)`,
while `IsSimpleModule` is `IsSimpleOrder (Submodule (U(L)) M)`.) -/
theorem isIrreducible_iff_isSimpleModule {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module (UniversalEnvelopingAlgebra R L) M]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι R x) • m = ⁅x, m⁆) :
    LieModule.IsIrreducible R L M ↔ IsSimpleModule (UniversalEnvelopingAlgebra R L) M := by
  rw [isSimpleModule_iff]
  exact (lieModuleSubmoduleEquiv hι).isSimpleOrder_iff

end Commons.RepresentationTheory.LieEnveloping