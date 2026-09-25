import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3Map
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction

/-!
# `Work.ShafarevichKoch.CoeffZ` -- the coefficient sequence `0 → ℤ →^2 ℤ → ℤ/2 → 0`

Hajir--Maire--Ramakrishna (`arXiv:2103.09508`, §1.2) read the Shafarevich--Koch relation bound
off the exact sequence

```
0 → H²(G,ℤ)/p → H²(G,ℤ/p) → H³(G,ℤ)[p] → 0
```

induced by the coefficient sequence `0 → ℤ --p--> ℤ → ℤ/p → 0` (with trivial `G`-action), whose
middle map is the connecting map `δ²` of `Cohomology3Map.lean`/`connecting2.lean`.  For `p = 2`
and `G` a pro-`2` group this is

```
0 → H²(G,ℤ)/2H²(G,ℤ) → H²(G,ℤ/2) → H³(G,ℤ)[2] → 0 ,
```

the sequence this chapter consumes: `H²(G,ℤ/2)` is the continuous cohomology group
`Work.RelatorRank.contH2 G`, and the two outer terms are bounded by Wingberg's duality
(`README.md` §18.2) by the units of the tower and by the class group.

This module provides the *coefficient* side of that sequence, written in the workspace's
conventions:

* `intTrivialAction`, `intDiscrete` : `ℤ` as a trivial discrete `G`-module;
* `intDoubleEqHom`, `intModTwoEqHom` : the two maps of the coefficient sequence;
* `zModTwoCoeffSES` : the short exact sequence `CoeffSES G ℤ ℤ (ZMod 2)`;
* `H2Map_zModTwoCoeffSES_f`, `H3Map_zModTwoCoeffSES_f` : the induced map on `H²`/`H³` of the
  *same* group is multiplication by `2` (this is what identifies the kernel of the coefficient
  map with `2·H²(G,ℤ)` and the image of the connecting map with the `2`-torsion of `H³(G,ℤ)`).

## Main declarations

* `Work.ShafarevichKoch.intTrivialAction`, `intDiscrete`, `intDoubleEqHom`, `intModTwoEqHom`,
  `zModTwoCoeffSES`, `mul_two_apply`;
* `Work.ShafarevichKoch.H2Map_zModTwoCoeffSES_f`, `H3Map_zModTwoCoeffSES_f`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

/-! ## `ℤ` as a trivial discrete module -/

/-- **The trivial action of a group on `ℤ`.** -/
@[reducible] def intTrivialAction (G : Type*) [Group G] : DistribMulAction G ℤ where
  smul _ n := n
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- **The trivial action of a group on `ℤ`**, as an instance (low priority, so that for `G = ℤ`
the canonical action of `ℤ` on itself is preferred). -/
instance (priority := 100) instTrivialDistribMulActionInt (G : Type*) [Group G] :
    DistribMulAction G ℤ := intTrivialAction G

/-- With the trivial action, `ℤ` is a discrete `G`-module: every stabiliser is all of `G`. -/
instance (priority := 100) instIsDiscreteGModuleInt (G : Type*) [Group G] [TopologicalSpace G] :
    IsDiscreteGModule G ℤ :=
  ⟨fun _ => IsLocallyConstant.const _⟩

section Coeff

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Multiplication by `2` on `ℤ`**, as an additive homomorphism. -/
def intDoubleHom : ℤ →+ ℤ where
  toFun n := 2 * n
  map_zero' := by norm_num
  map_add' a b := by ring

@[simp] lemma intDoubleHom_apply (n : ℤ) : intDoubleHom n = 2 * n := rfl

/-- Multiplication by `2` on `ℤ`, as a `G`-equivariant map for the trivial action. -/
def intDoubleEqHom : EqHom G ℤ ℤ where
  toAddMonoidHom := intDoubleHom
  map_smul' := fun σ a => by
    show intDoubleHom (σ • a) = σ • intDoubleHom a
    rw [show σ • a = a from rfl, show σ • intDoubleHom a = intDoubleHom a from rfl]

@[simp] lemma intDoubleEqHom_apply (n : ℤ) : intDoubleEqHom (G := G) n = 2 * n := rfl

end Coeff

section ModTwo

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance instTwoActionMod : DistribMulAction G (ZMod 2) := Work.RelatorRank.f2TrivialAction G
local instance instTwoDiscreteMod : IsDiscreteGModule G (ZMod 2) :=
  Work.RelatorRank.f2Discrete G

/-- **The reduction `ℤ → ℤ/2`.** -/
def intModTwoHom : ℤ →+ ZMod 2 where
  toFun n := (n : ZMod 2)
  map_zero' := Int.cast_zero
  map_add' a b := Int.cast_add a b

@[simp] lemma intModTwoHom_apply (n : ℤ) : intModTwoHom n = (n : ZMod 2) := rfl

/-- The reduction `ℤ → ℤ/2`, as a `G`-equivariant map for the trivial action. -/
def intModTwoEqHom : EqHom G ℤ (ZMod 2) where
  toAddMonoidHom := intModTwoHom
  map_smul' := fun σ a => by
    show intModTwoHom (σ • a) = σ • intModTwoHom a
    rw [show (σ • a : ℤ) = a from rfl, smul_zmodTwo_eq]

@[simp] lemma intModTwoEqHom_apply (n : ℤ) : intModTwoEqHom (G := G) n = (n : ZMod 2) := rfl

/-- **The coefficient sequence `0 → ℤ --2--> ℤ --mod 2--> ℤ/2 → 0`** (trivial `G`-action), the
sequence whose long exact sequence in cohomology gives HMR's
`0 → H²(G,ℤ)/2 → H²(G,ℤ/2) → H³(G,ℤ)[2] → 0`. -/
def zModTwoCoeffSES : CoeffSES G ℤ ℤ (ZMod 2) where
  f := intDoubleEqHom
  g := intModTwoEqHom
  injective_f := by
    intro a b h
    have h' : 2 * a = 2 * b := h
    omega
  surjective_g := by
    intro c
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) c with h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  exact := by
    intro b
    constructor
    · intro hb
      have hb' : ((b : ℤ) : ZMod 2) = 0 := hb
      have hdvd : (2 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hb'
      obtain ⟨a, ha⟩ := hdvd
      exact ⟨a, by show 2 * a = b; omega⟩
    · rintro ⟨a, rfl⟩
      show ((2 * a : ℤ) : ZMod 2) = 0
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [mul_comm, h2, mul_zero]

/-- The coefficient map `H²(G,ℤ) → H²(G,ℤ/2)` of the `ℤ`-power sequence is multiplication by
`2`, on the level of cocycles. -/
theorem H2Map_zModTwoCoeffSES_f_mk (z : Z2 G ℤ) :
    H2Map (zModTwoCoeffSES (G := G)).f (H2.mk z) = H2.mk (2 • z) := by
  rw [H2Map_mk]
  congr 1

/-- **The coefficient map `H²(G,ℤ) → H²(G,ℤ/2)` of the `ℤ`-power sequence is multiplication by
`2`** on the cohomology. -/
theorem H2Map_zModTwoCoeffSES_f (x : H2 G ℤ) :
    H2Map (zModTwoCoeffSES (G := G)).f x = 2 • x := by
  refine QuotientAddGroup.induction_on x ?_
  intro z
  show H2Map (zModTwoCoeffSES (G := G)).f (H2.mk z) = 2 • (H2.mk z : H2 G ℤ)
  rw [H2Map_zModTwoCoeffSES_f_mk]
  exact map_nsmul (QuotientAddGroup.mk' (B2' G ℤ)) 2 z

/-- The coefficient map `H³(G,ℤ) → H³(G,ℤ/2)`... on the level of cocycles: the `ℤ`-power
sequence induces an endomorphism of `H³(G,ℤ)`, multiplication by `2`. -/
theorem H3Map_zModTwoCoeffSES_f_mk (z : Z3 G ℤ) :
    H3Map (zModTwoCoeffSES (G := G)).f (H3.mk z) = H3.mk (2 • z) := by
  rw [H3Map_mk]
  congr 1

/-- **The coefficient map `H³(G,ℤ) → H³(G,ℤ/2)` is multiplication by `2` on `H³(G,ℤ)`.**  The
image of the connecting map of the `ℤ`-power sequence is therefore exactly the `2`-torsion
subgroup of `H³(G,ℤ)` (exactness at `H³(G,ℤ)`, `Work.ShafarevichKoch.exact_H3_A`). -/
theorem H3Map_zModTwoCoeffSES_f (x : H3 G ℤ) :
    H3Map (zModTwoCoeffSES (G := G)).f x = 2 • x := by
  refine QuotientAddGroup.induction_on x ?_
  intro z
  show H3Map (zModTwoCoeffSES (G := G)).f (H3.mk z) = 2 • (H3.mk z : H3 G ℤ)
  rw [H3Map_zModTwoCoeffSES_f_mk]
  exact map_nsmul (QuotientAddGroup.mk' (B3' G ℤ)) 2 z

end ModTwo

end Work.ShafarevichKoch
