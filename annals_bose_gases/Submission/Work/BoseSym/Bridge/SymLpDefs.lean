import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Perm.permAmb_mem_Hsub
import Submission.Work.BoseSym.Perm.symAvgAmb_fst
import Submission.Work.BoseSym.Perm.symAvgAmb_graphPoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the symmetrisation average as a continuous linear map on `L²`

The symmetrisation average of a function,
`symAvgF N f x = (N!)⁻¹ * ∑_σ f (actPerm σ x)`, is the average of the `N!`
permuted copies of `f`.  On the configuration space it is implemented by the
average of the isometries `permLp N σ` on `L²`; we package that average as the
continuous linear map `symLp N`, together with the two facts used by the
symmetric bridge:

* `symLp N` is a contraction, `‖symLp N u‖ ≤ ‖u‖`;
* it computes the first component of the symmetrisation average of the ambient
  space, `(symAvgAmb N p).1 = symLp N p.1`, so that in particular
  `l2Sq (graphPoint N L (symTest N L F)) = ‖symLp N (toLpTest F)‖ ^ 2`.

This module is the vocabulary shared with the delegated lemmas of the
`Work.BoseSym.Bridge` symmetric-bridge development; it contains only
definitions and elementary facts.
-/

namespace Work.BoseSym

open MeasureTheory Filter
open scoped Topology Real

noncomputable section

set_option autoImplicit false

/-- The canonical `L²` element attached to a test function: the function part of
its graph point. -/
noncomputable def toLpTest {N : ℕ} {L : ℝ} (F : testSub N L) : L2 N :=
  MemLp.toLp (F : Conf N → ℝ)
    (memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2))

/-- The function part of the graph point of a test function is `toLpTest F`. -/
lemma toLpTest_eq_fst {N : ℕ} {L : ℝ} (F : testSub N L) :
    (graphPoint N L F).1 = toLpTest F := rfl

/-- The permutation action on `L²` as a continuous linear map. -/
noncomputable def permLpC (N : ℕ) (σ : Equiv.Perm (Fin N)) : L2 N →L[ℝ] L2 N :=
  (Lp.compMeasurePreservingₗᵢ ℝ (tauPerm N σ) (measurePreserving_tauPerm N σ)).toContinuousLinearMap

/-- The symmetrisation average, as a continuous linear map on `L²`: the average
of the isometries `permLp N σ` over the symmetric group. -/
noncomputable def symLp (N : ℕ) : L2 N →L[ℝ] L2 N :=
  (Nat.factorial N : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), permLpC N σ

lemma symLp_apply {N : ℕ} (u : L2 N) :
    symLp N u = (Nat.factorial N : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), permLp N σ u := by
  simp only [symLp, permLpC, smul_apply, sum_apply, LinearIsometry.coe_toContinuousLinearMap]
  rfl

/-- `symLp N` is a contraction. -/
lemma norm_symLp_le {N : ℕ} (u : L2 N) : ‖symLp N u‖ ≤ ‖u‖ := by
  have hcard : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ℝ) = (Nat.factorial N : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hfac : (0 : ℝ) < (Nat.factorial N : ℝ) := by positivity
  have hsum : ‖∑ σ : Equiv.Perm (Fin N), permLp N σ u‖
      ≤ (Nat.factorial N : ℝ) * ‖u‖ := by
    calc ‖∑ σ : Equiv.Perm (Fin N), permLp N σ u‖
        ≤ ∑ σ : Equiv.Perm (Fin N), ‖permLp N σ u‖ := norm_sum_le _ _
      _ = ∑ _σ : Equiv.Perm (Fin N), ‖u‖ := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          exact norm_permLp σ u
      _ = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * ‖u‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Nat.factorial N : ℝ) * ‖u‖ := by rw [hcard]
  rw [symLp_apply, norm_smul,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (Nat.factorial N : ℝ)⁻¹)]
  calc (Nat.factorial N : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin N), permLp N σ u‖
      ≤ (Nat.factorial N : ℝ)⁻¹ * ((Nat.factorial N : ℝ) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖u‖ := by field_simp

/-- The first component of the symmetrisation average of the ambient space is
the symmetrisation average of the first component, as a continuous linear map. -/
lemma fst_symAvgAmb_eq_symLp {N : ℕ} (p : Amb N) :
    (symAvgAmb N p).1 = symLp N p.1 := by
  rw [symLp_apply]
  simp only [symAvgAmb, Prod.smul_fst, Prod.fst_sum, permAmb_fst]

/-- The `L²` norm of the graph point of the symmetrisation of a test function is
the norm of `symLp N` applied to the `L²` class of the test function. -/
lemma l2Sq_graphPoint_symTest {N : ℕ} {L : ℝ} (F : testSub N L) :
    l2Sq (graphPoint N L (symTest N L F)) = ‖symLp N (toLpTest F)‖ ^ 2 := by
  rw [show graphPoint N L (symTest N L F) = symAvgAmb N (graphPoint N L F) from
    (Perm.symAvgAmb_graphPoint F).symm]
  rw [l2Sq, fst_symAvgAmb_eq_symLp, toLpTest_eq_fst]

end

end Work.BoseSym
