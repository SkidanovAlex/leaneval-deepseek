import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxPairCount_eq_sum_compT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxPairQCount_eq_sum_compT`

The **ordered pair-`PQ` count** at the FS-faithful box projections in its *spectral* form.  With
`Pᵢ = boxPInd volA A i`, `Qⱼ = boxQInd volA A j` the commuting family of box projections
(`BoxSpectralDefs`), the count

    Σ_{q ∈ pairSet N} ∫_{abox N ℓ} (P_{q.1}(Q_{q.2}Φ))²

(`pairSet N` = ordered pairs of *distinct* particle indices) equals the weighted sum over the
three-way joint components `ψ_{S,T} = boxCompT volA A S T Φ`,

    Σ_{(S,T) ∈ disjPairs N} |S|·|T| · ∫_{abox N ℓ} (ψ_{S,T})² ,

because `n₀ n₊` (`n₀ = ΣⱼPⱼ`, `n₊ = ΣⱼQⱼ`) acts on the range of `boxCompT S T` by `|S|·|T|`.
This is the pair-`PQ` companion of `boxFlatCount_eq_sum_compT` (`|S|`-weight) and
`boxQCount_eq_sum_compT` (`|T|`-weight).

## Math

Three ingredients.

* **The `Q`-component decomposition** (`boxPairQCount_qdecomp`): on the box,
  `QⱼΦ = Σ_{p : j ∈ p.2} ψ_p`, from `boxCompT_sum_eq`, `agreeBox_boxQInd`, the finite-sum
  additivity `boxQInd_finset_sum_gen` and the eigenvalue rule `boxQInd_boxCompT`.
* **The per-ordered-pair spectral identity** (`boxPairQCount_pident`): applying `Pᵢ` to the
  previous decomposition (`agreeBox_boxPInd`, `boxPInd_finset_sum_gen`, `boxPInd_boxCompT`) gives
  `PᵢQⱼΦ = Σ_{p : i ∈ p.1, j ∈ p.2} ψ_p` on the box, and the components of distinct disjoint
  pairs are orthogonal there (`boxCompT_orth`), so `∫(PᵢQⱼΦ)² = Σ_{p : i∈p.1, j∈p.2} ∫(ψ_p)²`
  (`integral_sum_compT_sq`).
* **The counting/swap** (`sum_pairSet_filter_disjPairs_T`): exchanging the two finite sums turns
  the indicator `[i ∈ S][j ∈ T]` (with `(i,j)` ranging over the ordered pairs of distinct
  indices) into the multiplicity `|S|·|T|` — the fibre `{q ∈ pairSet N : q.1 ∈ S, q.2 ∈ T}` is
  exactly `S ×ˢ T` because disjointness makes `q.1 ≠ q.2` automatic
  (`Finset.card_product`).

The assembly is then a two-line `calc`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The `Q`-component decomposition on the box -/

/-- On the analysis box, `QⱼΦ` is the sum of the three-way joint components whose `Q`-slot set
contains `j`. -/
private theorem boxPairQCount_qdecomp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      UBBInputs8.boxQInd volA A j Φ x
        = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.2),
            boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  have hsum : ∀ y ∈ abox N ℓ, Φ y = ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y :=
    fun y hy => (boxCompT_sum_eq hℓ hvol hA hvolA hAc hΦc y hy).symm
  have h1 : UBBInputs8.boxQInd volA A j Φ x
      = UBBInputs8.boxQInd volA A j
          (fun y => ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y) x :=
    agreeBox_boxQInd hA hAc j hsum x hx
  have h2 : UBBInputs8.boxQInd volA A j
        (fun y => ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y) x
      = ∑ p ∈ disjPairs N, UBBInputs8.boxQInd volA A j (boxCompT volA A p.1 p.2 Φ) x :=
    boxQInd_finset_sum_gen volA A j x (disjPairs N)
      (fun p => boxCompT volA A p.1 p.2 Φ)
      (fun p _ => slotInt_of_bound hℓ hA hAc j x hx (hG p).1 (hG p).2.choose_spec)
  have h3 : (∑ p ∈ disjPairs N, UBBInputs8.boxQInd volA A j (boxCompT volA A p.1 p.2 Φ) x)
      = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.2), boxCompT volA A p.1 p.2 Φ x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p hp =>
      boxQInd_boxCompT hℓ hvol hA hvolA hAc (mem_disjPairs.mp hp) hΦc j x hx)
  rw [h1, h2, h3]

/-! ## 2. The per-ordered-pair spectral identity -/

/-- **The per-ordered-pair spectral identity.**  On the box,
`PᵢQⱼΦ = Σ_{p : i ∈ p.1, j ∈ p.2} ψ_p`, and the components of distinct disjoint pairs are
orthogonal there, so the box `L²`-norm of `PᵢQⱼΦ` is the sum of the squared norms of the
components whose `P`-slot (resp. `Q`-slot) set contains `i` (resp. `j`). -/
private theorem boxPairQCount_pident {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (i j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
          ∫ x in Submission.BoseGases.abox N ℓ,
            (boxCompT volA A p.1 p.2 Φ x) ^ 2 := by
  have hΦG : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  have hG : ∀ p : Finset (Fin N) × Finset (Fin N),
      GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦG
  -- the pointwise component decomposition of `PᵢQⱼΦ` on the box
  have hpt : ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
        = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
            boxCompT volA A p.1 p.2 Φ x := by
    intro x hx
    have hQ := boxPairQCount_qdecomp hℓ hvol hA hvolA hAc hΦc j
    calc UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x
        = UBBInputs8.boxPInd volA A i
            (fun y => ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.2),
              boxCompT volA A p.1 p.2 Φ y) x :=
            agreeBox_boxPInd hA hAc i hQ x hx
      _ = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.2),
            UBBInputs8.boxPInd volA A i (boxCompT volA A p.1 p.2 Φ) x :=
            boxPInd_finset_sum_gen volA A i x ((disjPairs N).filter (fun p => j ∈ p.2))
              (fun p => boxCompT volA A p.1 p.2 Φ)
              (fun p _ => slotInt_of_bound hℓ hA hAc i x hx (hG p).1 (hG p).2.choose_spec)
      _ = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.2),
            (if i ∈ p.1 then boxCompT volA A p.1 p.2 Φ x else 0) :=
            Finset.sum_congr rfl
              (fun p _ => boxPInd_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦc i x hx)
      _ = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
            boxCompT volA A p.1 p.2 Φ x := by
            conv_lhs => rw [Finset.sum_filter (s := disjPairs N) (p := fun p => j ∈ p.2)
              (f := fun p => if i ∈ p.1 then boxCompT volA A p.1 p.2 Φ x else 0)]
            conv_rhs => rw [Finset.sum_filter (s := disjPairs N)
              (p := fun p => i ∈ p.1 ∧ j ∈ p.2)
              (f := fun p => boxCompT volA A p.1 p.2 Φ x)]
            apply Finset.sum_congr rfl
            intro p _
            by_cases hi : i ∈ p.1 <;> by_cases hj : j ∈ p.2 <;> simp [hi, hj]
  calc (∫ x in abox N ℓ,
          (UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∫ x in abox N ℓ,
          (∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
            boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by rw [hpt x hx])
    _ = ∑ p ∈ (disjPairs N).filter (fun p => i ∈ p.1 ∧ j ∈ p.2),
          ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
          integral_sum_compT_sq hℓ hvol hA hvolA hAc hΦc _
            (fun p hp => mem_disjPairs.mp (Finset.mem_filter.mp hp).1)

/-! ## 3. The counting/swap identity on `pairSet` -/

/-- The number of ordered pairs `q ∈ pairSet N` of **distinct** indices with `q.1 ∈ S`, `q.2 ∈ T`
(`S ⊥ T`), weighted by `c`: `Σ_{q ∈ pairSet N} [q.1 ∈ S][q.2 ∈ T]·c = |S|·|T|·c`. -/
private theorem sum_pairSet_ite_mem_disj {N : ℕ} (S T : Finset (Fin N)) (hST : Disjoint S T)
    (c : ℝ) :
    (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ T then c else 0))
      = ((S.card : ℝ) * (T.card : ℝ)) * c := by
  classical
  have h1 : (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ T then c else 0))
      = (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ T then (1 : ℝ) else 0)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : q.1 ∈ S ∧ q.2 ∈ T <;> simp [h]
  have h2 : (∑ q ∈ pairSet N, (if q.1 ∈ S ∧ q.2 ∈ T then (1 : ℝ) else 0))
      = ((S.card : ℝ) * (T.card : ℝ)) := by
    have hset : (pairSet N).filter (fun q => q.1 ∈ S ∧ q.2 ∈ T) = S ×ˢ T := by
      ext q
      rw [show pairSet N = (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun p => p.1 ≠ p.2) from rfl,
        Finset.filter_filter]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun hEq => Finset.disjoint_left.mp hST (hEq ▸ h1) h2, h1, h2⟩
    rw [Finset.sum_boole, hset, Finset.card_product, Nat.cast_mul]
  rw [h1, h2]

/-- **The counting/swap identity of the pair-`PQ` count.**  Summing over the ordered pairs
`q ∈ pairSet N` the mass of the components whose `P`-slot (resp. `Q`-slot) set contains `q.1`
(resp. `q.2`) and exchanging the two finite sums gives, for each component, the multiplicity
`|p.1|·|p.2|` of ordered pairs it carries. -/
private theorem sum_pairSet_filter_disjPairs_T {N : ℕ}
    (F : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ q ∈ pairSet N,
        ∑ p ∈ (disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.2), F p)
      = ∑ p ∈ disjPairs N, ((p.1.card : ℝ) * (p.2.card : ℝ)) * F p := by
  classical
  calc (∑ q ∈ pairSet N,
          ∑ p ∈ (disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.2), F p)
      = ∑ q ∈ pairSet N, ∑ p ∈ disjPairs N,
            (if q.1 ∈ p.1 ∧ q.2 ∈ p.2 then F p else 0) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_filter]
    _ = ∑ p ∈ disjPairs N, ∑ q ∈ pairSet N,
            (if q.1 ∈ p.1 ∧ q.2 ∈ p.2 then F p else 0) := Finset.sum_comm
    _ = ∑ p ∈ disjPairs N, ((p.1.card : ℝ) * (p.2.card : ℝ)) * F p :=
        Finset.sum_congr rfl
          (fun p hp => sum_pairSet_ite_mem_disj p.1 p.2 (mem_disjPairs.mp hp) (F p))

/-! ## 4. The spectral form of the pair-`PQ` count -/

theorem boxPairQCount_eq_sum_compT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    (∑ p ∈ Work.BoseFixB1S.disjPairs N, (p.1.card : ℝ) * (p.2.card : ℝ) *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) ^ 2)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A p.1
              (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2 := by
  have h1 : (∑ q ∈ pairSet N,
        ∫ x in abox N ℓ,
          (UBBInputs8.boxPInd volA A q.1 (UBBInputs8.boxQInd volA A q.2 Φ) x) ^ 2)
      = ∑ q ∈ pairSet N,
          ∑ p ∈ (disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.2),
            ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2 :=
    Finset.sum_congr rfl
      (fun q _ => boxPairQCount_pident hℓ hvol hA hvolA hAc hΦc q.1 q.2)
  have h2 := sum_pairSet_filter_disjPairs_T
    (fun p => ∫ x in abox N ℓ, (boxCompT volA A p.1 p.2 Φ x) ^ 2)
  rw [← h2, ← h1]

end Work.BoseFixB1S
