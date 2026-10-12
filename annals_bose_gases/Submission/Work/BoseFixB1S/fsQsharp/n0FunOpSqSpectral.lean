import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Gen.n0FunOpSqrtPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.fsQsharp.n0FunOpSqSpectral`

**The spectral (Parseval) identity for the `n₀` functional calculus at the squared `L²` norm.**

For a state `ψ` that is measurable and bounded on the analysis box (`GoodState ℓ ψ`) and *any*
function `g : ℝ → ℝ` of the occupation number, the squared `L²(abox N ℓ)`-norm of `g(n₀)ψ` is the
weighted sum of the squared norms of its sector components:

    ∫_{abox N ℓ} (g(n₀)ψ)² = Σ_{S : Finset (Fin N)} g(|S|)² · ∫_{abox N ℓ} (P_S ψ)² ,

where `n0FunOp volA A g` is the corpus's functional calculus `Σ_{k≤N} g k • n0LagrangeOp k`
(equivalently `Σ_S g(|S|) · n0ProjOp volA A S`, by `n0FunOp_eq_sum_card`) and
`P_S = n0ProjOp volA A S = ∏_{i∈S}P_{B,i}∏_{i∉S}(1−P_{B,i})` are the subset idempotents of the
FS box projections `P_{B,i} = UBBInputs8.boxPInd volA A i`.

## Proof

Purely the two structural facts already in the corpus, both available for `GoodState` states (no
continuity needed):

* `n0FunOp_eq_sum_card`: `g(n₀) = Σ_S g(|S|)·P_S`, so the left-hand side is the squared norm of a
  finite linear combination of the sectors, with coefficients `c S = g(|S|)`;
* `n0SectorOrthB1_aux` (via `n0SectorOrthB1`): the sectors are **pairwise orthogonal** in
  `L²(abox N ℓ)` — for a slot `j ∈ S \ T`, `P_j` is self-adjoint on the box
  (`boxPIndSelfAdjoint`) and `P_j` acts on the sectors with eigenvalues `1` and `0`
  (`n0IterEigen`), so `∫ P_Sψ · P_Tψ = ∫ (P_jP_Sψ)·P_Tψ = ∫ P_Sψ·(P_jP_Tψ) = 0`;
* `n0ProjOp_pairing_integrableB1`: the pairwise products are integrable on the box.

The expansion of the square of the finite sum (`boxSqSumWeightedOrthB1_self`, i.e.
`boxSqSumExpandB1` followed by the collapse of the double sum along the diagonal using the
orthogonality) then gives the claim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S.fsQsharp

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The pairwise orthogonality of the `n₀`-sectors, for box-bounded states.**  Packaged form of
`n0SectorOrthB1_aux` with the slot extracted from `S ≠ T`: for two distinct finite subsets of the
species set, the box pairing of the corresponding subset idempotents vanishes. -/
theorem n0ProjOp_orth_univ {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {ψ : X N → ℝ} (hψ : Work.BoseFixB1S.GoodState ℓ ψ)
    {S T : Finset (Fin N)} (hST : S ≠ T) :
    (∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S ψ x
        * Work.BoseFixB1S.n0ProjOp volA A T ψ x) = 0 := by
  by_cases h : ∃ j : Fin N, j ∈ S ∧ j ∉ T
  · obtain ⟨j, hjS, hjT⟩ := h
    exact Work.BoseFixB1S.n0SectorOrthB1_aux hℓ hvol hA hvolA hAc hψ S T j hjS hjT
  · push_neg at h
    have hex : ∃ j : Fin N, j ∈ T ∧ j ∉ S := by
      by_contra hc
      push_neg at hc
      exact hST (Finset.Subset.antisymm h hc)
    obtain ⟨j, hjT, hjS⟩ := hex
    have hkey :=
      Work.BoseFixB1S.n0SectorOrthB1_aux hℓ hvol hA hvolA hAc hψ T S j hjT hjS
    rw [show (∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A S ψ x
            * Work.BoseFixB1S.n0ProjOp volA A T ψ x)
          = ∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A T ψ x
            * Work.BoseFixB1S.n0ProjOp volA A S ψ x from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    exact hkey

theorem n0FunOpSqSpectral {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (g : ℝ → ℝ)
    {ψ : Submission.BoseGases.X N → ℝ} (hψ : Work.BoseFixB1S.GoodState ℓ ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.n0FunOp volA A g ψ x) ^ 2)
      = ∑ S : Finset (Fin N), (g (S.card : ℝ)) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.n0ProjOp volA A S ψ x) ^ 2 := by
  classical
  have hprod : ∀ p ∈ (Finset.univ : Finset (Finset (Fin N))),
      ∀ q ∈ (Finset.univ : Finset (Finset (Fin N))),
      IntegrableOn (fun x : X N => Work.BoseFixB1S.n0ProjOp volA A p ψ x
        * Work.BoseFixB1S.n0ProjOp volA A q ψ x) (abox N ℓ) volume :=
    fun p _ q _ => Work.BoseFixB1S.n0ProjOp_pairing_integrableB1 hℓ hvol hA hvolA hAc hψ p q
  have horth : ∀ p ∈ (Finset.univ : Finset (Finset (Fin N))),
      ∀ q ∈ (Finset.univ : Finset (Finset (Fin N))), p ≠ q →
      (∫ x in abox N ℓ, Work.BoseFixB1S.n0ProjOp volA A p ψ x
        * Work.BoseFixB1S.n0ProjOp volA A q ψ x) = 0 :=
    fun p _ q _ hpq => n0ProjOp_orth_univ hℓ hvol hA hvolA hAc hψ hpq
  rw [Work.BoseFixB1S.n0FunOp_eq_sum_card]
  exact Work.BoseFixB1S.boxSqSumWeightedOrthB1_self (s := Finset.univ) hprod horth

end Work.BoseFixB1S.fsQsharp
