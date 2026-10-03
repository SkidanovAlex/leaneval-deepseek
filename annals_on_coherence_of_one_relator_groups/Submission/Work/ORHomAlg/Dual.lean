/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The dual of a module over a group algebra

For a group `G`, a commutative ring `K` and a left `K[G]`-module `M`, the *dual* `M*` is the same
additive group with the action `g · m = g⁻¹ · m`; it is a right `K[G]`-module.  This is the
construction denoted `M*` in Jaikin-Zapirain--Linton, Lemma 5.2 (2).  The key ingredient is the
antipode, the anti-automorphism `x ↦ x*` of `K[G]` determined by `g* = g⁻¹`, realised here as the
ring isomorphism `antipodeEquiv : K[G] ≃+* (K[G])ᵐᵒᵖ`.

## Main definitions

* `Work.ORHomAlg.antipodeEquiv K G : K[G] ≃+* (K[G])ᵐᵒᵖ`, `single g c ↦ op (single g⁻¹ c)`;
* `Work.ORHomAlg.dualLeft K G M`, the `Module (K[G])ᵐᵒᵖ` structure on a left `K[G]`-module;
* `Work.ORHomAlg.dualRight K G L`, the `Module (K[G])` structure on a right `K[G]`-module;
* `Work.ORHomAlg.DualMod M`, a copy of `M` on which the dual structures are *installed*, together
  with the compatibility instances (`IsScalarTower`, `SMulCommClass`) needed to form the diagonal
  `K[G]`-structures on tensor products (`DiagTensorDefs`).

The point of the type synonym `DualMod` is that the module structures occurring in the statement of
JL Lemma 5.2 (2) are *determined by the data*, rather than being ambient: this is what makes the
statement true (the canonical comparison maps fail without the compatibility instances).
-/
import Submission.Work.ORHomAlg.Dual.exists_antipodeEquiv
import Mathlib.Algebra.Algebra.Opposite

namespace Work.ORHomAlg

universe u v

open MonoidAlgebra

/-- The antipode of a group algebra: the ring isomorphism `K[G] ≃+* (K[G])ᵐᵒᵖ` sending `g` to
`g⁻¹` (i.e. `single g c ↦ op (single g⁻¹ c)`). -/
noncomputable def antipodeEquiv (K : Type u) [CommSemiring K] (G : Type v) [Group G] :
    MonoidAlgebra K G ≃+* (MonoidAlgebra K G)ᵐᵒᵖ :=
  Classical.choose (Work.ORHomAlg.Dual.exists_antipodeEquiv K G)

theorem antipodeEquiv_single (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (g : G) (c : K) :
    antipodeEquiv K G (MonoidAlgebra.single g c) =
      MulOpposite.op (MonoidAlgebra.single g⁻¹ c) :=
  Classical.choose_spec (Work.ORHomAlg.Dual.exists_antipodeEquiv K G) g c

/-- The dual `M*` of a left `K[G]`-module `M`, as a right `K[G]`-module: the same additive group
with `op x • m = x* • m`, where `x ↦ x*` is the antipode. -/
noncomputable def dualLeft (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M] :
    Module (MonoidAlgebra K G)ᵐᵒᵖ M :=
  Module.compHom M (antipodeEquiv K G).symm.toRingHom

/-- The dual `L*` of a right `K[G]`-module `L`, as a left `K[G]`-module: the same additive group
with `x • l = l · x*`, where `x ↦ x*` is the antipode. -/
noncomputable def dualRight (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L] :
    Module (MonoidAlgebra K G) L :=
  Module.compHom L (antipodeEquiv K G).toRingHom

@[simp]
theorem dualLeft_op_smul (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    (x : MonoidAlgebra K G) (m : M) :
    letI := dualLeft K G M
    (MulOpposite.op x) • m = (antipodeEquiv K G).symm (MulOpposite.op x) • m := rfl

@[simp]
theorem dualRight_smul (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
    (x : MonoidAlgebra K G) (l : L) :
    letI := dualRight K G L
    x • l = antipodeEquiv K G x • l := rfl

theorem dualRight_single_smul (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
    (g : G) (l : L) :
    letI := dualRight K G L
    (MonoidAlgebra.single g (1 : K)) • l =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • l := by
  rw [dualRight_smul, antipodeEquiv_single]

theorem dualLeft_single_op_smul (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    (g : G) (m : M) :
    letI := dualLeft K G M
    (MulOpposite.op (MonoidAlgebra.single g (1 : K))) • m =
      (MonoidAlgebra.single g⁻¹ (1 : K)) • m := by
  letI := dualLeft K G M
  rw [dualLeft_op_smul]
  have h : antipodeEquiv K G (MonoidAlgebra.single g⁻¹ (1 : K)) =
      MulOpposite.op (MonoidAlgebra.single g (1 : K)) := by
    rw [antipodeEquiv_single]; simp
  have h2 : (antipodeEquiv K G).symm (MulOpposite.op (MonoidAlgebra.single g (1 : K))) =
      MonoidAlgebra.single g⁻¹ (1 : K) := by
    rw [← h, RingEquiv.symm_apply_apply]
  rw [h2]

theorem antipodeEquiv_algebraMap (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (c : K) :
    antipodeEquiv K G (algebraMap K (MonoidAlgebra K G) c) =
      MulOpposite.op (algebraMap K (MonoidAlgebra K G) c) := by
  rw [show algebraMap K (MonoidAlgebra K G) c = MonoidAlgebra.single (1 : G) c from rfl,
    antipodeEquiv_single, inv_one]

/-! ## The type synonym `DualMod`

`DualMod M` is a copy of `M` on which the *dual* module structures are installed.  We use a
genuine type synonym (rather than a `Module` instance supplied as a hypothesis) so that the module
structures occurring in the statement of JL Lemma 5.2 (2) are determined by the data. -/

/-- `DualMod M` is a copy of `M` on which the dual module structures are installed: the copy of a
left `R`-module is a right `R`-module and conversely, the action of `g` being the action of `g⁻¹`.
All other structure (`AddCommGroup`, `Module K`, and the original module structures) is transported
from `M` along the identity. -/
def DualMod (M : Type u) : Type u := M

namespace DualMod

/-- The identity bijection `M ≃ DualMod M`. -/
def of (M : Type u) : M ≃ DualMod M := Equiv.refl M

instance instAddCommGroup (M : Type u) [AddCommGroup M] : AddCommGroup (DualMod M) :=
  inferInstanceAs (AddCommGroup M)

instance instModuleK (K : Type v) (M : Type u) [Semiring K] [AddCommGroup M] [Module K M] :
    Module K (DualMod M) := inferInstanceAs (Module K M)

/-- The dual of a right `K[G]`-module, as a left `K[G]`-module. -/
noncomputable instance instModuleOfRight (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G)ᵐᵒᵖ M] :
    Module (MonoidAlgebra K G) (DualMod M) :=
  dualRight K G M

/-- The original right `K[G]`-module structure, transported to `DualMod M`. -/
noncomputable instance instModuleOppositeOfRight (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G)ᵐᵒᵖ M] :
    Module (MonoidAlgebra K G)ᵐᵒᵖ (DualMod M) :=
  inferInstanceAs (Module (MonoidAlgebra K G)ᵐᵒᵖ M)

/-- The dual of a left `K[G]`-module, as a right `K[G]`-module. -/
noncomputable instance instModuleOppositeOfLeft (K : Type u) [CommSemiring K] (G : Type v)
    [Group G] (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M] :
    Module (MonoidAlgebra K G)ᵐᵒᵖ (DualMod M) :=
  dualLeft K G M

@[simp]
theorem instModuleOfRight_smul (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G)ᵐᵒᵖ M]
    (x : MonoidAlgebra K G) (m : DualMod M) :
    x • m = antipodeEquiv K G x • m :=
  dualRight_smul K G M x m

theorem instModuleOppositeOfLeft_smul (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    (y : (MonoidAlgebra K G)ᵐᵒᵖ) (m : DualMod M) :
    y • m = (antipodeEquiv K G).symm y • m :=
  dualLeft_op_smul K G M (MulOpposite.unop y) m

/-- `op (single g 1) • m = single g⁻¹ 1 • m` for the dual of a left `K[G]`-module. -/
theorem op_single_smul_eq_single_smul_of_left (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    (g : G) (m : DualMod M) :
    (MulOpposite.op (MonoidAlgebra.single g (1 : K))) • m =
      (MonoidAlgebra.single g⁻¹ (1 : K)) • m :=
  dualLeft_single_op_smul K G M g m

/-- The hypothesis `hA` of the Brown isomorphism for the dual of a right `K[G]`-module: the left
structure installed on `DualMod M` is the dual of the right structure of `M`. -/
theorem single_smul_eq_op_inv_smul_of_right (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G)ᵐᵒᵖ M]
    (g : G) (m : DualMod M) :
    (MonoidAlgebra.single g (1 : K)) • m =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • m :=
  dualRight_single_smul K G M g m

/-- The hypothesis `hA` of the Brown isomorphism for the dual of a left `K[G]`-module: here the
*original* left action is the one installed on `DualMod M`, and the right structure is its dual. -/
theorem single_smul_eq_op_inv_smul_of_left (K : Type u) [CommSemiring K] (G : Type v) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    (g : G) (m : DualMod M) :
    (MonoidAlgebra.single g (1 : K)) • m =
      (MulOpposite.op (MonoidAlgebra.single g⁻¹ (1 : K))) • m := by
  have h := dualLeft_single_op_smul K G M g⁻¹ m
  rw [inv_inv] at h
  exact h.symm

end DualMod

/-! ## Compatibility of the dual structures with the `K`-action -/

section Compat

variable (K : Type u) [Field K] (G : Type v) [Group G]

theorem smul_op_one (c : K) :
    c • (MulOpposite.op (1 : MonoidAlgebra K G)) =
      (MulOpposite.op (algebraMap K (MonoidAlgebra K G) c) : (MonoidAlgebra K G)ᵐᵒᵖ) := by
  show MulOpposite.op (c • (1 : MonoidAlgebra K G)) = _
  rw [Algebra.smul_def, mul_one]

/-- In a right `K[G]`-module whose `K`-action is compatible with the `K[G]`-action, the action of
`op (algebraMap c)` is the action of `c`. -/
theorem op_algebraMap_smul (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ M] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ M]
    (c : K) (m : M) :
    (MulOpposite.op (algebraMap K (MonoidAlgebra K G) c)) • m = c • m := by
  have h1 : c • (MulOpposite.op (1 : MonoidAlgebra K G)) =
      MulOpposite.op (algebraMap K (MonoidAlgebra K G) c) := smul_op_one K G c
  have h2 : (MulOpposite.op (1 : MonoidAlgebra K G)) • m = m := one_smul _ m
  have h := IsScalarTower.smul_assoc c (MulOpposite.op (1 : MonoidAlgebra K G)) m
  rw [h1, h2] at h
  exact h

end Compat

namespace DualMod

variable (K : Type u) [Field K] (G : Type v) [Group G]

instance instIsScalarTowerOppositeOfRight (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ M] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ M] :
    IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ (DualMod M) :=
  ‹IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ M›

instance instSMulCommClassOppositeOfRight (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ M] [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ M] :
    SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (DualMod M) :=
  ‹SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ M›

instance instIsScalarTowerOfLeft (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    IsScalarTower K (MonoidAlgebra K G) (DualMod M) :=
  ‹IsScalarTower K (MonoidAlgebra K G) M›

instance instSMulCommClassOfLeft (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M] :
    SMulCommClass K (MonoidAlgebra K G) (DualMod M) :=
  ‹SMulCommClass K (MonoidAlgebra K G) M›

/-! ### Compatibility instances for the dual of a right `K[G]`-module -/

instance instIsScalarTowerOfRight (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ M] [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ M] :
    IsScalarTower K (MonoidAlgebra K G) (DualMod M) where
  smul_assoc c x m := by
    show antipodeEquiv K G (c • x) • m = c • (antipodeEquiv K G x • m)
    rw [Algebra.smul_def]
    show (antipodeEquiv K G (algebraMap K (MonoidAlgebra K G) c * x)) • m
        = c • (antipodeEquiv K G x • m)
    rw [map_mul, antipodeEquiv_algebraMap, mul_smul]
    exact op_algebraMap_smul K G M c (antipodeEquiv K G x • m)

instance instSMulCommClassOfRight (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G)ᵐᵒᵖ M] [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ M] :
    SMulCommClass K (MonoidAlgebra K G) (DualMod M) where
  smul_comm c x m := by
    show c • (antipodeEquiv K G x • m) = antipodeEquiv K G x • (c • m)
    exact SMulCommClass.smul_comm c (antipodeEquiv K G x) m


/-! ### Compatibility instances for the dual of a left `K[G]`-module -/

/-- `(antipodeEquiv K G).symm (op (algebraMap c)) = algebraMap c`. -/
theorem symm_op_algebraMap (c : K) :
    (antipodeEquiv K G).symm (MulOpposite.op (algebraMap K (MonoidAlgebra K G) c)) =
      algebraMap K (MonoidAlgebra K G) c := by
  rw [← antipodeEquiv_algebraMap K G c, RingEquiv.symm_apply_apply]

theorem smul_op_eq_mul_op (y : (MonoidAlgebra K G)ᵐᵒᵖ) (c : K) :
    c • y = y * MulOpposite.op (algebraMap K (MonoidAlgebra K G) c) := by
  show MulOpposite.op (c • (MulOpposite.unop y)) = _
  rw [Algebra.smul_def, MulOpposite.op_mul, MulOpposite.op_unop]

instance instIsScalarTowerOppositeOfLeft (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M] :
    IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ (DualMod M) where
  smul_assoc c y m := by
    show (antipodeEquiv K G).symm (c • y) • m = c • ((antipodeEquiv K G).symm y • m)
    rw [smul_op_eq_mul_op K G y c, map_mul, symm_op_algebraMap,
      ← Algebra.commutes (R := K) c ((antipodeEquiv K G).symm y), ← Algebra.smul_def]
    exact IsScalarTower.smul_assoc c ((antipodeEquiv K G).symm y) m

instance instSMulCommClassOppositeOfLeft (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M] :
    SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (DualMod M) where
  smul_comm c y m := by
    show c • ((antipodeEquiv K G).symm y • m) = (antipodeEquiv K G).symm y • (c • m)
    exact SMulCommClass.smul_comm c ((antipodeEquiv K G).symm y) m


end DualMod

end Work.ORHomAlg
