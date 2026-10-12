import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.RTFoldMoment
import Submission.Work.BoseFixB1.flatPieceRT_eigen
import Submission.Work.BoseFixB1.flatPiece_orthogonal
import Submission.Work.BoseFixB1S.boxPairQCount_eqB1
import Submission.Work.BoseFixB1S.n0OpEqSpectral
import Submission.Work.BoseFixB1S.n0SpectralMomentsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0PairPairingB1` — the `n₀`-pairing of the box `QP`-cross term

For the FS-faithful box projections (`FS eq:HBU`)

  `Pᵢ = UBBInputs8.boxPInd volA A i`  (`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`),
  `Qᵢ = UBBInputs8.boxQInd volA A i = 1_A(·ᵢ)Φ − PᵢΦ`,

and a state `Φ` supported (a.e. on the box) in `A^N`, the doubly summed `QP`-cross term is

    ∑ᵢ ∑ⱼ ∫_{abox N ℓ} (QᵢΦ)(PⱼΦ) = N·n₀ − n₀ − cS₂,

with `n₀ = boxFlatCount volA ℓ A Φ = ∑ᵢ∫(PᵢΦ)²` and
`cS₂ = boxPairCount volA ℓ A Φ = ∑_{p∈pairSet N}∫(P_{p.1}P_{p.2}Φ)²` (`pairSet` = *ordered*
distinct pairs, so `cS₂` counts each unordered pair twice).

## Math

`1_A(·ᵢ)Φ = Φ` a.e. on the box (the support hypothesis), so `QᵢΦ = Φ − PᵢΦ` a.e. and every
summand splits:

    ∫ (QᵢΦ)(PⱼΦ) = ∫ Φ(PⱼΦ) − ∫ (PᵢΦ)(PⱼΦ).

Summing over the `N²` ordered pairs,

* `∑ᵢ∑ⱼ ∫ Φ(PⱼΦ) = N·∑ⱼ ∫ Φ(PⱼΦ) = N·n₀` (the summand does not depend on `i`), using the
  self-integral identity `∫Φ(PⱼΦ) = ∫(PⱼΦ)²` (`Q0C.one_self_N`);
* `∑ᵢ∑ⱼ ∫(PᵢΦ)(PⱼΦ) = ∑ᵢ ∫(PᵢΦ)² + ∑_{p∈pairSet N}∫(P_{p.1}P_{p.2}Φ)² = n₀ + cS₂`
  (`Q0C.sum_univ_univ_eq` for the diagonal/off-diagonal splitting and `Q0C.pair_mixed_N` for
  the off-diagonal summands).

The integrability side conditions of the splitting are supplied by the bounds
`|Φ| ≤ C`, `|PᵢΦ| ≤ C` on the compact box (`exists_abox_bound`, `abs_boxPInd_le`) via
`integrableOn_mul_of_bound`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

/-- A state supported (a.e. on the box) in `A^N` is fixed by the slot-`i` box indicator. -/
private theorem ae_indicator_mul_self {N : ℕ} {ℓ : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) (i : Fin N) :
    (fun x : Submission.BoseGases.X N =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] Φ := by
  filter_upwards [hsupp] with x hx
  by_cases h : Φ x = 0
  · rw [h, mul_zero]
  · rw [Set.indicator_of_mem (hx h i)]
    simp

/-- **The per-pair splitting** of the `QP`-cross term at the box projections: using the support
hypothesis `1_A(·ᵢ)Φ = Φ` a.e., `QᵢΦ = Φ − PᵢΦ` a.e. and the integral splits. -/
private theorem boxQInd_mul_boxPInd_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    (i j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = (∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound (N := N) hℓ hΦc
  have hPim : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦc.measurable
  have hPjm : Measurable (Work.UBBInputs8.boxPInd volA A j Φ) :=
    measurable_boxPInd volA A hA j hΦc.measurable
  have hPib : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    abs_boxPInd_le (N := N) hℓ hvol hA hvolA hAc i hCb
  have hPjb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A j Φ x| ≤ C :=
    abs_boxPInd_le (N := N) hℓ hvol hA hvolA hAc j hCb
  have hI1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound (N := N) hℓ hΦc.measurable hPjm hCb hPjb
  have hI2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound (N := N) hℓ hPim hPjm hPib hPjb
  have hae : (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x : Submission.BoseGases.X N =>
        Φ x * Work.UBBInputs8.boxPInd volA A j Φ x
          - Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x) := by
    filter_upwards [ae_indicator_mul_self hsupp i] with x hx
    simp only [Work.UBBInputs8.boxQInd]
    rw [hx]
    ring
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x * Work.UBBInputs8.boxPInd volA A j Φ x
            - Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x) :=
        MeasureTheory.integral_congr_ae hae
    _ = (∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j Φ x :=
        MeasureTheory.integral_sub hI1 hI2

theorem n0PairPairingB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
      = (N : ℝ) * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          - Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  -- `volA` is the real-valued volume of `A`.
  have hvolA' : volA
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  -- The per-pair splitting of the integrand.
  have hpair : ∀ i j : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
        = (∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
          - ∫ x in Submission.BoseGases.abox N ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x :=
    fun i j => boxQInd_mul_boxPInd_eq hℓ hvol hA hvolA hAc hΦc hsupp i j
  -- The diagonal contribution `∑ᵢ ∫(PᵢΦ)²`.
  have hdiag : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
      = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
    rw [Work.BoseFixB1S.boxFlatCount]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  -- The off-diagonal contribution `∑_{p ∈ pairSet} ∫(P_{p.1}P_{p.2}Φ)²`.
  have hPairSet : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x)
      = Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    rw [Work.BoseFixB1S.boxPairCount]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    exact Q0C.pair_mixed_N hℓ hvol hA hvolA' hAc
      (by simpa [Submission.BoseGases.pairSet] using (Finset.mem_filter.mp hp).2) hΦc
  -- The first (flat) family: the summand does not depend on the outer index.
  have hFlat : (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = (N : ℝ) * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
    have hinner : ∀ _i : Fin N,
        (∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
          = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
      intro i
      rw [Work.BoseFixB1S.boxFlatCount]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Q0C.one_self_N hℓ hvol hA hvolA' hAc j hΦc
    calc (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
        = ∑ _i : Fin N, Work.BoseFixB1S.boxFlatCount volA ℓ A Φ :=
          Finset.sum_congr rfl (fun i _ => hinner i)
      _ = (N : ℝ) * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- The second (pair) family: diagonal plus the off-diagonal `pairSet` sum.
  have hPair : (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        + Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    rw [Q0C.sum_univ_univ_eq (fun i j : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)]
    show (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
        + (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x)
        = Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          + Work.BoseFixB1S.boxPairCount volA ℓ A Φ
    rw [hdiag, hPairSet]
  -- Assembly.
  have hstep : (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
      = (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
          - (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ x
                * Work.UBBInputs8.boxPInd volA A j Φ x) := by
    have h1 : (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x))
        = ∑ i : Fin N, ∑ j : Fin N,
            ((∫ x in Submission.BoseGases.abox N ℓ,
                Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
              - ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.UBBInputs8.boxPInd volA A i Φ x
                    * Work.UBBInputs8.boxPInd volA A j Φ x) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpair i j))
    have h2 : (∑ i : Fin N, ∑ j : Fin N,
            ((∫ x in Submission.BoseGases.abox N ℓ,
                Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
              - ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.UBBInputs8.boxPInd volA A i Φ x
                    * Work.UBBInputs8.boxPInd volA A j Φ x))
        = ∑ i : Fin N,
            ((∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
              - ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.UBBInputs8.boxPInd volA A i Φ x
                    * Work.UBBInputs8.boxPInd volA A j Φ x) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_sub_distrib _ _)
    rw [h1, h2, Finset.sum_sub_distrib]
  rw [hstep, hFlat, hPair]
  ring

end Work.BoseFixB1S
