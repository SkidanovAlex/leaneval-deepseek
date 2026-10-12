import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxPairQCount_eq_sum_compT
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxVarLeNmulQCountB1
import Submission.Work.BoseFixB1S.boxPairQCount_eqB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.a0A2QJointPairQCountLe` — the joint pair-`PQ` count against `n₀·n₊`

At the FS-faithful box projections `Pᵢ = UBBInputs8.boxPInd volA A i`,
`Qᵢ = UBBInputs8.boxQInd volA A i`, and for a state `Φ` that is continuous, **normalised**
(`∫_{abox} Φ² = 1`) and **localised** (`Φ = 0` a.e. off the occupancy sector `A^N`), the fully
`|S|·|T|`-weighted sum of the three-way joint component masses is dominated by the product of the
two counts,

    Σ_{(S,T), S⊥T} |S|·|T|·∫_{abox} (ψ_{S,T})²  ≤  n₀ · n₊ ,

where `n₀ = boxFlatCount volA ℓ A Φ = Σᵢ∫(PᵢΦ)²`, `n₊ = boxQCount volA ℓ A Φ = Σᵢ∫(QᵢΦ)²`
and `ψ_{S,T} = boxCompT volA A S T Φ`.

## Math

Three PROVED corpus facts, plus the hypotheses `hcS2`, `hnorm`, `hsupp`.

* `boxPairQCount_eq_sum_compT` identifies the sum of the statement (over `disjPairs N`, the
  spectral indexing of the components) with the ordered pair-`PQ` count
  `⟨n₀n₊⟩ = Σ_{p ∈ pairSet N} ∫(P_{p.1}(Q_{p.2}Φ))²`.
* `boxPairQCount_eqB1` bounds that count by `(N−1)·n₀ − cS₂`,
  `cS₂ = boxPairCount volA ℓ A Φ`.
* `boxVarLeNmulQCount_count_identity` is FS's identity `n₀ + n₊ = N`, which holds exactly because
  `Φ` is normalised and supported in `A^N` (`hsupp` forces `Σᵢ 1_A(xᵢ) = N` a.e. where `Φ ≠ 0`).

Together with `hcS2 : n₀² − n₀ ≤ cS₂` this gives

    ⟨n₀n₊⟩ ≤ (N−1)n₀ − cS₂ ≤ (N−1)n₀ − (n₀² − n₀) = n₀(N − n₀) = n₀·n₊ .

The two support hypotheses (`hnorm`, `hsupp`) are essential and are not removable: without them the
identity `n₀ + n₊ = N` fails and the statement is false
(cf. `FINDING_S293_boxCrossJointGen_FALSE.md`).
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

theorem a0A2QJointPairQCountLe {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    (hcS2 : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ) :
    (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) * (p.2.card : ℝ) *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  -- `Work.BoseFixB1.disjPairs` and `Work.BoseFixB1S.disjPairs` are the same finset
  have hdp : Work.BoseFixB1.disjPairs N = Work.BoseFixB1S.disjPairs N := rfl
  -- the spectral sum is the ordered pair-`PQ` count `⟨n₀n₊⟩`
  rw [hdp,
    boxPairQCount_eq_sum_compT (N := N) (ℓ := ℓ) (volA := volA) (A := A)
      hℓ hvol hA hvolA hAc hΦc]
  have hpair := boxPairQCount_eqB1 (N := N) (ℓ := ℓ) (volA := volA) (A := A)
    hℓ hvol hA hvolA hAc hΦc
  have hcount := boxVarLeNmulQCount_count_identity (N := N) (ℓ := ℓ) (V := volA)
    hℓ hvol hA hvolA hAc hΦc hnorm hsupp
  set S := Work.BoseFixB1S.boxFlatCount volA ℓ A Φ with hS
  set nq := Work.BoseFixB1S.boxQCount volA ℓ A Φ with hnq
  set Pc := Work.BoseFixB1S.boxPairCount volA ℓ A Φ with hPc
  -- (`set` has already replaced the occurrences in `hpair`, `hcount` and `hcS2`)
  -- arithmetic: `(N−1)S − Pc ≤ (N−1)S − (S²−S) = S(N−S) = S·n₊`
  have hN : (N : ℝ) = S + nq := hcount.symm
  have hkey : ((N : ℝ) - 1) * S - Pc ≤ S * nq := by
    rw [hN]
    nlinarith [hcS2]
  linarith [hpair, hkey]

end Work.BoseFixB1S
