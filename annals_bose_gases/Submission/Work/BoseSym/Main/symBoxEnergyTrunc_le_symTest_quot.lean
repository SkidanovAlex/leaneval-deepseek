import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseSym.Bridge.symBoxQuot_eq_dirForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — every symmetrised test function bounds the symmetric box energy

The truncated symmetric box energy `symBoxEnergyTrunc N L v M` is, by definition,
the infimum of the truncated Rayleigh quotient

    ((∫_box Σ_{i,k} (∂_{ik} Ψ)²) + (∫_box Vtrunc N v M · Ψ²)) / (∫_box Ψ²)

over the symmetric (permutation invariant) trial states `Ψ : SymBox N L`.  Hence
it is at most the value of that quotient at *any* such state.

The state we evaluate it at here is the symmetrisation of an arbitrary smooth
test function `F` supported in the open box: `symAvg N F` is `C^∞`, supported in
`openBox N L ⊆ interior (box N L)`, and permutation invariant, so it is a
legitimate element of `SymBox N L`.  Its Rayleigh quotient is exactly the
Dirichlet quotient of the graph point of `symTest N L F`, by the bridge lemmas
converting `gSq`, `potSq` and `l2Sq` of a graph point into box integrals.

The nontrivial side condition is that the symmetrised function is nonzero: this is
where the hypothesis `l2Sq (graphPoint N L (symTest N L F)) ≠ 0` enters (a
vanishing `L²` norm forces the function to vanish).  Nonzero is needed both for
the `nezero` field of `CInfty0Box` and to guarantee that the infimum is over a
nonempty family (`ciInf_le` needs the quotients to be bounded below, which
follows from nonnegativity of each summand).
-/

namespace Work.BoseSym.Main

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

set_option autoImplicit false

/-- The truncated Rayleigh quotient of a symmetric trial state, with the two box
integrals parenthesised separately; `symBoxEnergyTrunc` is by definition its
infimum over `Ψ : SymBox N L`. -/
noncomputable def symTruncQuot (N : ℕ) (L : ℝ) (v : E3 → ℝ) (M : ℝ) (Ψ : SymBox N L) : ℝ :=
  ((intBox N L (fun x => ∑ i : Fin N, ∑ k : Fin 3,
      (fderiv ℝ (Ψ : Conf N → ℝ) x (eDir N i k)) ^ 2))
    + (intBox N L (fun x => Vtrunc N v M x * ((Ψ : Conf N → ℝ) x) ^ 2)))
    / (intBox N L (fun x => ((Ψ : Conf N → ℝ) x) ^ 2))

/-- The truncated symmetric box energy is the infimum of the truncated quotients
(definitionally). -/
theorem symBoxEnergyTrunc_eq_iInf_symTruncQuot {N : ℕ} {L : ℝ} {v : E3 → ℝ} {M : ℝ} :
    symBoxEnergyTrunc N L v M = ⨅ Ψ : SymBox N L, symTruncQuot N L v M Ψ := rfl

/-- The truncated quotient of a symmetric trial state is the Dirichlet quotient of
the graph point of the associated test function. -/
theorem symTruncQuot_eq_dirForm {N : ℕ} {L : ℝ} {v : E3 → ℝ} {M : ℝ} (Ψ : SymBox N L) :
    symTruncQuot N L v M Ψ
      = dirForm (Vtrunc N v M) (graphPoint N L (symBoxToTest N L Ψ))
        / l2Sq (graphPoint N L (symBoxToTest N L Ψ)) := by
  rw [symTruncQuot, dirForm, Bridge.gSq_graphPoint_box, Bridge.potSq_graphPoint_box,
    Bridge.l2Sq_graphPoint_box]
  simp only [symBoxToTest_coe]

theorem symBoxEnergyTrunc_le_symTest_quot {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv : 0 ≤ v)
    {M : ℝ} (hM : 0 ≤ M) (F : testSub N L)
    (h : l2Sq (graphPoint N L (symTest N L F)) ≠ 0) :
    symBoxEnergyTrunc N L v M ≤
      dirForm (Vtrunc N v M) (graphPoint N L (symTest N L F))
        / l2Sq (graphPoint N L (symTest N L F)) := by
  -- the symmetrisation of `F` does not vanish (otherwise its `L²` norm would)
  have hne : (symAvg N (F : Conf N → ℝ)) ≠ 0 := by
    intro h0
    apply h
    have h0' : (symTest N L F : Conf N → ℝ) = 0 := h0
    rw [Bridge.l2Sq_graphPoint_box, h0']
    simp [intBox]
  -- the symmetrisation is supported in the open box, hence in the interior
  have hsup : Function.support (symAvg N (F : Conf N → ℝ)) ⊆
      tsupport fun x => ∑ σ : Equiv.Perm (Fin N), (F : Conf N → ℝ) (actPerm N σ x) := by
    intro x hx
    simp only [Function.mem_support] at hx
    refine subset_tsupport _ ?_
    simp only [Function.mem_support]
    intro hsum
    exact hx (by simp only [symAvg, hsum, mul_zero])
  have hts : tsupport (symAvg N (F : Conf N → ℝ)) ⊆ interior (box N L) :=
    ((closure_minimal hsup (isClosed_tsupport _)).trans (permSum_tsupport_openBox F.2.2)).trans
      (openBox_subset_interior_box (N := N) L)
  -- the symmetrised function is a symmetric trial state
  let Ψ₀ : SymBox N L :=
    ⟨⟨symAvg N (F : Conf N → ℝ), (symAvg_contDiff F.2.1).contDiffOn, hts, hne⟩,
      symAvg_sym N (F : Conf N → ℝ)⟩
  -- and it is the test function `symTest N L F`
  have hbt : symBoxToTest N L Ψ₀ = symTest N L F := Subtype.ext rfl
  -- each truncated quotient is nonnegative, so the infimum is bounded below
  have hbdd : BddBelow (Set.range (symTruncQuot N L v M)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨Ψ, rfl⟩
    rw [symTruncQuot, intBox, intBox, intBox]
    refine div_nonneg (add_nonneg ?_ ?_) ?_
    · exact setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x =>
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
    · exact setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (Vtrunc_nonneg hv hM x) (sq_nonneg _))
    · exact setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
  calc symBoxEnergyTrunc N L v M
      = ⨅ Ψ : SymBox N L, symTruncQuot N L v M Ψ :=
        symBoxEnergyTrunc_eq_iInf_symTruncQuot
    _ ≤ symTruncQuot N L v M Ψ₀ := ciInf_le hbdd Ψ₀
    _ = dirForm (Vtrunc N v M) (graphPoint N L (symTest N L F))
          / l2Sq (graphPoint N L (symTest N L F)) := by
        rw [symTruncQuot_eq_dirForm, hbt]

end Work.BoseSym.Main
