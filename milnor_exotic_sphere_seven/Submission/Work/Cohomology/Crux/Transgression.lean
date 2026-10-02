import Mathlib
import Submission.Work.Cohomology.RelMVLes
import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.relCohMVDefs
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.cokernel_map_shortExact
import Submission.Work.Cohomology.cokernel_biprod_map_iso
import Submission.Work.Cohomology.Crux.cokernel_map_shortExact_canonical
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.cap_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transgression for the relative Mayer–Vietoris sequence (canonical maps)

The relative Mayer–Vietoris short exact sequence of `Submission/Work/Cohomology/relMV_shortExact.lean`
is produced by an abstract `∃` (through `cokernel_map_shortExact`), so its maps are opaque; for the
computation of the compatibility of the cap product with the connecting map one needs the
*canonical* maps `cokernel.map ...`.  This file fixes those canonical maps (`cruxF`, `cruxG`),
records the short exactness, and sets up the chain level statements used for the transgression.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The middle term of the canonical relative Mayer–Vietoris sequence. -/
abbrev cruxMid (X : TopCat) (A U V : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))

/-- **The first canonical map of the relative Mayer–Vietoris sequence.** -/
noncomputable def cruxF (X : TopCat) (A U V : Set X) :
    relMVUV X A U V ⟶ cruxMid X A U V :=
  cokernel.map (f := (relMVv U V A).τ₁) (f' := (relMVv U V A).τ₂)
    (mvLeftSmallA U V A) (mvLeftSmall U V) (relMVv U V A).comm₁₂

/-- **The second canonical map of the relative Mayer–Vietoris sequence.** -/
noncomputable def cruxG (X : TopCat) (A U V : Set X) :
    cruxMid X A U V ⟶ relMVTopC X A U V :=
  cokernel.map (f := (relMVv U V A).τ₂) (f' := (relMVv U V A).τ₃)
    (mvRightSmallA U V A) (mvRightSmall U V) (relMVv U V A).comm₂₃

/-- The composite of the two canonical relative Mayer–Vietoris maps is zero. -/
theorem cruxZero (X : TopCat) (A U V : Set X) :
    cruxF X A U V ≫ cruxG X A U V = 0 :=
  Classical.choose (Work.Cohomology.Crux.cokernel_map_shortExact_canonical (mvSmallA_shortExact U V A)
    (mvSmall_shortExact U V) (relMVv U V A) (mono_subInclChain U V Set.inter_subset_left)
    (mono_biprod_map (mono_subInclChain U V Set.inter_subset_left)
      (mono_subInclChain U V Set.inter_subset_left))
    (mono_smallInToSmall U V A))

/-- **The canonical relative Mayer–Vietoris complex.** -/
noncomputable def cruxShort (X : TopCat) (A U V : Set X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (cruxF X A U V) (cruxG X A U V) (cruxZero X A U V)

/-- **The canonical relative Mayer–Vietoris complex is short exact.** -/
theorem cruxShort_shortExact (X : TopCat) (A U V : Set X) : (cruxShort X A U V).ShortExact :=
  Classical.choose_spec (Work.Cohomology.Crux.cokernel_map_shortExact_canonical (mvSmallA_shortExact U V A)
    (mvSmall_shortExact U V) (relMVv U V A) (mono_subInclChain U V Set.inter_subset_left)
    (mono_biprod_map (mono_subInclChain U V Set.inter_subset_left)
      (mono_subInclChain U V Set.inter_subset_left))
    (mono_smallInToSmall U V A))

/-- The connecting homomorphism `H_{n+1}(C^{U,V}(X,A)) ⟶ H_n(U∩V, U∩V∩A)` of the canonical
relative Mayer–Vietoris sequence. -/
noncomputable def cruxδ (X : TopCat) (A U V : Set X) (n : ℕ) :
    (relMVTopC X A U V).homology (n + 1) ⟶ (relMVUV X A U V).homology n :=
  (cruxShort_shortExact X A U V).δ (n + 1) n (by simp [ComplexShape.down])

end

end Work.Cohomology
