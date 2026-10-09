/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bounded approximation by the logarithmic unit embedding

Let `K` be a number field and let

`logEmbedding K : (𝓞 K)ˣ → logSpace K = {w : InfinitePlace K // w ≠ w₀} → ℝ`

be the logarithmic embedding of the units, `logEmbedding K u w = mult w * log (w u)`.  Dirichlet's
unit theorem says that the image of `logEmbedding` is a full `ℤ`-lattice (`unitLattice K`) in the
finite dimensional real vector space `logSpace K`, so the quotient of `logSpace K` by this lattice
is compact: for every `b : logSpace K` there is a unit `u` such that the coordinates of
`b - logEmbedding K u` are bounded by a constant depending only on the field.

This is the archimedean "approximation by units" input in the classical proof that the norm-one
idèle class group `𝕀¹_K ⧸ Kˣ` is compact (see e.g. Neukirch, *Algebraic Number Theory*,
Chapter III §5, or Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter XII).

The proof is a direct application of the fundamental domain of the lattice spanned by a real basis
all of whose vectors are logarithmic embeddings of units (`unitLogBasis` below): rounding the
coordinates of `b` on that basis gives an element of the lattice at distance at most
`∑ i, ‖unitLogBasis i‖`.

## Main definitions

* `NK.GlobalCFT.IdeleClassGroup.unitLogBasis`: a real basis of `logSpace K` whose vectors are all
  logarithmic embeddings of units,
* `NK.GlobalCFT.IdeleClassGroup.unitLogBound`: the constant `∑ i, ‖unitLogBasis K i‖`.

## Main results

* `NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_unit_logEmbedding_bound`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace NumberField.Units Module
open NumberField.Units.dirichletUnitTheorem

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- A real basis of the logarithmic space `logSpace K` all of whose vectors are logarithmic
embeddings of units of `𝓞 K`.  It is built from the fundamental system of units
(`NumberField.Units.fundSystem`). -/
def unitLogBasis (K : Type*) [Field K] [NumberField K] :
    Basis (Fin (rank K)) ℝ (logSpace K) :=
  basisOfIsMaxRank (isMaxRank_fundSystem K)

/-- The vectors of `unitLogBasis K` are logarithmic embeddings of units. -/
theorem unitLogBasis_apply (i : Fin (rank K)) :
    unitLogBasis K i = logEmbedding K (Additive.ofMul (fundSystem K i)) :=
  basisOfIsMaxRank_apply _ i

/-- The uniform constant controlling the size of the fundamental domain of the unit lattice with
respect to the basis `unitLogBasis`. -/
def unitLogBound (K : Type*) [Field K] [NumberField K] : ℝ := by
  classical
  exact ∑ i, ‖unitLogBasis K i‖

/-- Every vector of the basis `unitLogBasis K` lies in the unit lattice. -/
theorem unitLogBasis_mem_unitLattice :
    Set.range (unitLogBasis K) ⊆ (unitLattice K : Set (logSpace K)) := by
  rintro v ⟨i, rfl⟩
  rw [unitLogBasis_apply]
  exact Submodule.mem_map.mpr ⟨Additive.ofMul (fundSystem K i), trivial, rfl⟩

/-- The uniform constant `unitLogBound K` is nonnegative. -/
theorem unitLogBound_nonneg : 0 ≤ unitLogBound K := by
  classical
  exact Finset.sum_nonneg fun i _ => norm_nonneg _

/-- **Approximation by units in the logarithmic embedding.**  For every `b` in the logarithmic
space there is a unit `u` of `𝓞 K` whose logarithmic embedding is within the uniform distance
`unitLogBound K` of `b` in every coordinate `w ≠ w₀`. -/
theorem exists_unit_logEmbedding_close (b : logSpace K) :
    ∃ u : (𝓞 K)ˣ, ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |b w - w.val.mult * Real.log (w.val (u : K))| ≤ unitLogBound K := by
  classical
  have hle : Submodule.span ℤ (Set.range (unitLogBasis K)) ≤ unitLattice K :=
    Submodule.span_le.mpr unitLogBasis_mem_unitLattice
  have hmem : ((ZSpan.floor (unitLogBasis K) b : Submodule.span ℤ
      (Set.range (unitLogBasis K))) : logSpace K) ∈ unitLattice K :=
    hle (ZSpan.floor (unitLogBasis K) b).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hmem
  refine ⟨x.toMul, fun w => ?_⟩
  have hx' : logEmbedding K x = ((ZSpan.floor (unitLogBasis K) b : Submodule.span ℤ
      (Set.range (unitLogBasis K))) : logSpace K) := hx
  have hfrac : b - ((ZSpan.floor (unitLogBasis K) b :
      Submodule.span ℤ (Set.range (unitLogBasis K))) : logSpace K) =
        ZSpan.fract (unitLogBasis K) b :=
    (ZSpan.fract_apply _ _).symm
  have hcomp : logEmbedding K x w = w.val.mult * Real.log (w.val (x.toMul : K)) :=
    logEmbedding_component x.toMul w
  rw [← hcomp, hx', ← Pi.sub_apply, hfrac, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ w).trans (ZSpan.norm_fract_le _ _)

/-- **The unit lattice is cocompact in the logarithmic space.**  There is a constant `R ≥ 0` such
that every element `b` of `logSpace K` is, in every coordinate `w ≠ w₀`, within distance `R` of the
logarithmic embedding of some unit of `𝓞 K`. -/
theorem globalCFT_exists_unit_logEmbedding_bound {K : Type*} [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ b : NumberField.Units.dirichletUnitTheorem.logSpace K,
      ∃ u : (NumberField.RingOfIntegers K)ˣ,
        ∀ w : {w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          |b w - w.val.mult * Real.log (w.val (u : K))| ≤ R :=
  ⟨unitLogBound K, unitLogBound_nonneg, fun b => exists_unit_logEmbedding_close b⟩

end NK.GlobalCFT.IdeleClassGroup
