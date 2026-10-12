import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_hopCompTWeightedOrthAe_g
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_hopQIndDecomp_g
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_integral_child_sub_kappa_g
import Submission.Work.BoseFixB1.SectorAux.boxCrossPart_sub_twoMuP_eq_operatorB1_g
import Submission.Work.BoseFixB1.SectorAux.boxPInd_rungF_pointwise_g
import Submission.Work.BoseFixB1.SectorAux.hopBracketDecomp_g
import Submission.Work.BoseFixB1.SectorAux.pIndOrth_g
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.SectorAux.measHopExpansionFibCorr`

The hopping expansion of the sliding-box cross term, at a state `Φ` that is only **measurable and
bounded on the analysis box** (instead of continuous), and with the **uncentred** fibre
`fib = w1Fibre ℓ (wSmall1Pair h M ℓ d u)` on the right-hand side — the form the payment
estimates of the sector layer use:

  `(V/2)·(boxCrossPart V ℓ A w₁ Φ − 2μ·Σᵢ∫(QᵢΦ)·fib(xᵢ)·(PᵢΦ))
     = Σᵢ Σ_{p ∈ hopPairSet i} (|p.1| − 1 − μV)·∫ ψ_{cᵢ(p)}·fib(xᵢ)·ψ_p`

with `V = boxMass ℓ d u`, `A = dlBox ℓ d u`, `ψ_{S,T} = Work.BoseFixB1S.boxCompT V A S T Φ` and
`cᵢ(p) = (p.1.erase i, insert i p.2)`.

## Route

This is the statement of `Work.BoseFixB1S.a0A2QJointExpansionFib` with the regularity hypothesis
on `Φ` relaxed from `Continuous` to `Measurable ∧ bounded on the box`.  Exactly as there, the
argument is

1. the **fibre-centred identity** `boxCrossPart − 2μ·P = (2/V)·Σᵢ∫(QᵢΦ)·(fib(xᵢ) − κ)·(Pᵢ(rungF)
   − (1+μV)PᵢΦ)` (`Work.BoseFixB1.boxCrossPart_centred`), which uses continuity only to *produce*
   a bound of `Φ` on the compact box and its measurability;
2. the **bracket decomposition** `eq:Q1n0` and the **`Q`-decomposition** `QᵢΦ = Σ_{q∋i} ψ_q`,
   again only through `Work.BoseFixB1S.GoodState`;
3. the **collapse** of the `Q`-sum onto the child `cᵢ(p)` along the orthogonality of the joint
   components (`Work.BoseFixB1S.hopCollapseGen`, stated for arbitrary `Φ`);
4. the **uncentring** of each edge, `fib(xᵢ) − κ ↦ fib(xᵢ)`, which is the vanishing of
   `∫ ψ_{cᵢ(p)}·ψ_p`.

All the `Continuous`-hypothesis lemmas of the corpus that these steps call are used here in their
`Work.BoseFixB1S.GoodState` form, proved in the companion modules of this directory (imported above).  The only
non-bookkeeping inputs are the fibre a.e.-strong measurability and the fibre bound on `acube ℓ`,
both of which the corpus supplies for `w1Fibre ℓ (wSmall1Pair h M ℓ d u)` (via
`Work.BoseFixB1.q1Fib_aem_bound`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1.SectorAux

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## 1. The fibre-centred cross part at a `Work.BoseFixB1S.GoodState` -/

/-- `Work.BoseFixB1.boxCrossPart_centred` (equivalently `Work.BoseFixB1S.boxCrossPartCentredB1S`)
at a state which is only measurable and bounded on the analysis box. -/
private theorem boxCrossCentred_g {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) :
    Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x)
            * Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x))
      = (2 / Work.SmallBoxSliding.boxMass ℓ d u)
        * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                  - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                      (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                    / Work.SmallBoxSliding.boxMass ℓ d u)
              * ((Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i
                    (Work.BoseFixB1.rungF (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) Φ) x)
                  - (1 + μ * Work.SmallBoxSliding.boxMass ℓ d u)
                    * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                        (Submission.BoseGases.dlBox ℓ d u) i Φ x))) := by
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  set W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    Submission.BoseGases.wSmall1Pair h M ℓ d u with hWdef
  set fib : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.w1Fibre ℓ W with hfibdef
  set F : Submission.BoseGases.X N → ℝ := Work.BoseFixB1.rungF V A Φ with hFdef
  set κ : ℝ := Work.BoseFixB1S.boxM1 ℓ A W / V with hκdef
  -- ## basic box data
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVpos : 0 < V := hvol
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hVeq' : V = ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A).toReal := by
    rw [← MeasureTheory.Measure.real_def]; exact hVeq
  -- ## the fibre facts
  have hFmAes : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    rw [hfibdef, hWdef]
    have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    exact Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (f := Submission.BoseGases.g0 v h) hint.aestronglyMeasurable.aemeasurable
  have hCf : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |fib z| ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi * _root_.BoseGases.a v)) := by
    intro z _
    rw [hfibdef, hWdef]
    exact Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
      hM hℓ hd hR hRχ u z
  -- ## bounds for the state (from the given box bound, made nonnegative)
  set CΦ : ℝ := max Cb 0 with hCΦdef
  have hΦb' : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ := by
    intro x hx
    exact le_trans (hΦb x hx) (le_max_left _ _)
  have hPb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k Φ x| ≤ CΦ :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hVpos hAmeas hVeq' hAc k hΦb'
  have hQb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A k Φ x| ≤ 2 * CΦ := by
    intro k x hx
    have hP := hPb k x hx
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x k)| ≤ 1 := by
      by_cases hk : x k ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hk]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x k) * Φ x| ≤ CΦ := by
      rw [abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x k)| * |Φ x| ≤ 1 * CΦ :=
            mul_le_mul hind (hΦb' x hx) (abs_nonneg _) (by norm_num)
        _ = CΦ := one_mul CΦ
    have hQ : Work.UBBInputs8.boxQInd V A k Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x k) * Φ x
          - Work.UBBInputs8.boxPInd V A k Φ x := rfl
    rw [hQ]
    calc |A.indicator (fun _ => (1 : ℝ)) (x k) * Φ x - Work.UBBInputs8.boxPInd V A k Φ x|
          ≤ |A.indicator (fun _ => (1 : ℝ)) (x k) * Φ x|
            + |Work.UBBInputs8.boxPInd V A k Φ x| := abs_sub _ _
      _ ≤ CΦ + CΦ := add_le_add h1 hP
      _ = 2 * CΦ := by ring
  have hFb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |F x| ≤ N * CΦ := by
    intro x hx
    have hPk : ∀ k : Fin N, |Work.UBBInputs8.boxPInd V A k Φ x| ≤ CΦ := fun k => hPb k x hx
    have hFval : F x = ∑ j : Fin N, Work.UBBInputs8.boxPInd V A j Φ x := by
      rw [hFdef]
      rfl
    rw [hFval]
    calc |∑ j : Fin N, Work.UBBInputs8.boxPInd V A j Φ x| ≤ ∑ j : Fin N, (CΦ : ℝ) :=
          le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => hPk j))
      _ = N * CΦ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hPFb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k F x| ≤ N * CΦ :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hVpos hAmeas hVeq' hAc k hFb
  -- ## measurability
  have hQm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxQInd V A k Φ) :=
    fun k => Work.SlotWord.measurable_boxQInd V A hAmeas k hΦm
  have hPm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxPInd V A k Φ) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd V A hAmeas k hΦm
  have hFmm : Measurable F := by
    have hFval : F = fun x => ∑ j : Fin N, Work.UBBInputs8.boxPInd V A j Φ x := by
      rw [hFdef]
      rfl
    rw [hFval]
    exact Finset.measurable_sum Finset.univ (fun j _ => hPm j)
  have hPFm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxPInd V A k F) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd V A hAmeas k hFmm
  -- ## the two orthogonality identities
  have hZ1 : ∀ k : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k F x) = 0 := by
    intro k
    have hsa := Work.BoseFixB1S.boxPIndSelfAdjoint (N := N) (ℓ := ℓ) (volA := V) hℓ hVpos
      hAmeas hVeq' hAc k (Φ := F) (Ψ := Work.UBBInputs8.boxQInd V A k Φ)
      hFmm hFb (hQm k) (hQb k)
    have hcomm : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k F x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A k F x * Work.UBBInputs8.boxQInd V A k Φ x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring
    rw [hcomm, hsa]
    have hzero : (fun x : Submission.BoseGases.X N =>
        F x * Work.UBBInputs8.boxPInd V A k (Work.UBBInputs8.boxQInd V A k Φ) x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict
        (Submission.BoseGases.abox_measurable N ℓ)] with x hx
      rw [Work.BoseFixB1S.boxPInd_boxQInd_self_zero (volA := V) (A := A) hℓ hVpos hAmeas
        hVeq' hAc k ⟨hΦm, Cb, hΦb⟩ x hx, mul_zero]
    rw [MeasureTheory.integral_congr_ae hzero]
    simp
  have hZ2 : ∀ k : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k Φ x) = 0 := by
    intro k
    have horth := pIndOrth_g (N := N) (ℓ := ℓ) (volA := V) hℓ hVpos hAmeas
      hVeq' hAc k hΦm hΦb
    have hfun : (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k Φ x)
        = fun x => Work.UBBInputs8.boxPInd V A k Φ x *
            (A.indicator (fun _ => (1 : ℝ)) (x k) * Φ x
              - Work.UBBInputs8.boxPInd V A k Φ x) := by
      funext x
      simp only [Work.UBBInputs8.boxQInd]
      ring
    rw [hfun]
    exact horth
  -- ## the per-slot zero of the bracket
  have hZX : ∀ k : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x)) = 0 := by
    intro k
    have hI1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k F x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hQm k) (hPFm k) (hQb k) (hPFb k)
    have hI2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k Φ x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hQm k) (hPm k) (hQb k) (hPb k)
    have hI3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (1 + μ * V) * (Work.UBBInputs8.boxQInd V A k Φ x
          * Work.UBBInputs8.boxPInd V A k Φ x))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := hI2.const_mul _
    have hsplit : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
      = (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k F x)
        - (1 + μ * V) * (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k Φ x) := by
      rw [show (fun x : Submission.BoseGases.X N =>
            Work.UBBInputs8.boxQInd V A k Φ x *
              (Work.UBBInputs8.boxPInd V A k F x
                - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
          = fun x => (Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k F x)
              - (1 + μ * V) * (Work.UBBInputs8.boxQInd V A k Φ x
                  * Work.UBBInputs8.boxPInd V A k Φ x)
          from by funext x; ring]
      rw [MeasureTheory.integral_sub hI1 hI3, MeasureTheory.integral_const_mul]
    rw [hsplit, hZ1 k, hZ2 k]
    ring
  -- ## the pointwise identification of the bracket
  have hpt : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A k Φ) x)
          - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x
        = Work.UBBInputs8.boxPInd V A k F x
          - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x := by
    intro k x hx
    have h2 := boxPInd_rungF_pointwise_g (volA := V) (A := A) hℓ hVpos hAmeas hVeq' hAc k
      hΦm hΦb x hx
    have hF' : F = fun y => ∑ j : Fin N, Work.UBBInputs8.boxPInd V A j Φ y := by
      rw [hFdef]
      rfl
    rw [← h2, ← hF']
  -- ## step 1: replace the bracket
  have hAB : (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * fib (x k) *
          ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A k Φ) x)
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
      = ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * fib (x k) *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    rw [hpt k x hx]
  -- ## step 2: the fibre centring
  have hCen : (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * (fib (x k) - κ) *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
      = ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * fib (x k) *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x) := by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hXIb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd V A k F x
          - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x| ≤ N * CΦ + |1 + μ * V| * CΦ := by
      intro x hx
      calc |Work.UBBInputs8.boxPInd V A k F x
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x|
            ≤ |Work.UBBInputs8.boxPInd V A k F x|
              + |(1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x| := abs_sub _ _
        _ = |Work.UBBInputs8.boxPInd V A k F x|
              + |1 + μ * V| * |Work.UBBInputs8.boxPInd V A k Φ x| := by rw [abs_mul]
        _ ≤ N * CΦ + |1 + μ * V| * CΦ :=
            add_le_add (hPFb k x hx)
              (mul_le_mul_of_nonneg_left (hPb k x hx) (abs_nonneg _))
    have hm1 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd V A k Φ x *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x)|
          ≤ (2 * CΦ) * (N * CΦ + |1 + μ * V| * CΦ) := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (hQb k x hx) (hXIb x hx) (abs_nonneg _) (by positivity)
    have hsm : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxQInd V A k Φ x *
            (Work.UBBInputs8.boxPInd V A k F x
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      ((hQm k).mul ((hPFm k).sub ((hPm k).const_mul _))).aestronglyMeasurable
    have hIfib : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A k Φ x *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x)) * fib (x k))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1.integrableOn_abox_slot_mul hℓ k hFmAes hCf hsm hm1
    have hCfsub : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z - κ| ≤
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M)
            * (8 * Real.pi * _root_.BoseGases.a v)) + |κ| := by
      intro z hz
      exact le_trans (abs_sub _ _) (add_le_add (hCf z hz) le_rfl)
    have hIfibm : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A k Φ x *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x)) * (fib (x k) - κ))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      Work.BoseFixB1.integrableOn_abox_slot_mul hℓ k
        (F := fun z => fib z - κ) (hFmAes.sub aestronglyMeasurable_const) hCfsub hsm hm1
    have hI1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd V A k Φ x * (fib (x k) - κ) *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      hIfibm.congr (by filter_upwards with x; ring)
    have hI2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd V A k Φ x * fib (x k) *
          (Work.UBBInputs8.boxPInd V A k F x
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
      hIfib.congr (by filter_upwards with x; ring)
    rw [← MeasureTheory.integral_sub hI1 hI2]
    rw [show (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxQInd V A k Φ x * (fib (x k) - κ) *
            (Work.UBBInputs8.boxPInd V A k F x
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x)
          - Work.UBBInputs8.boxQInd V A k Φ x * fib (x k) *
            (Work.UBBInputs8.boxPInd V A k F x
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x))
        = fun x => -(κ * (Work.UBBInputs8.boxQInd V A k Φ x *
            (Work.UBBInputs8.boxPInd V A k F x
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A k Φ x)))
        from by funext x; ring]
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, hZX k]
    ring
  -- ## the previous lemma
  have hprev : Work.BoseFixB1.boxCrossPart V ℓ A W Φ
      - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd V A i Φ x * fib (x i)
            * Work.UBBInputs8.boxPInd V A i Φ x)
      = (2 / V) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd V A i Φ x * fib (x i) *
            ((∑ j : Fin N,
                Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A i Φ x)) := by
    simpa only [hVdef, hAdef, hWdef, hfibdef] using
      (boxCrossPart_sub_twoMuP_eq_operatorB1_g (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
        (M := M) hM (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol (N := N) (Φ := Φ) hΦm hΦb)
  rw [hprev]
  congr 1
  exact hAB.trans hCen.symm

/-! ## 2. The expansion core at a `Work.BoseFixB1S.GoodState` -/

/-- `Work.BoseFixB1S.boxCrossExpansionB1S.expansionCore` at a state which is only measurable and
bounded on the analysis box: the centred cross part, decomposed along the hopping edges. -/
private theorem expansionCore_g {N : ℕ} {ℓ V μ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} {fib : EuclideanSpace ℝ (Fin 3) → ℝ} {Cf : ℝ}
    (hℓ : 0 < ℓ) (hVpos : 0 < V) (hAmeas : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
    (hfibaesm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    (hcent : Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x))
      = (2 / V) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x)
              * (fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V)
              * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                  - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x))))
    (horth : ∀ (i : Fin N) (S T S' T' : Finset (Fin N)), Disjoint S T → Disjoint S' T' →
      ∀ j : Fin N, j ≠ i → Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT V A S T Φ x * (fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V)
          * Work.BoseFixB1S.boxCompT V A S' T' Φ x) = 0) :
    (V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x)))
      = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (((p.1.card : ℝ) - 1 - μ * V)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x
                  * (fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V)
                  * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) := by
  classical
  set δ : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => fib z - Work.BoseFixB1S.boxM1 ℓ A w₁ / V
    with hδ
  -- ## box data and fibre bounds
  have hCube0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ Submission.BoseGases.acube ℓ := by
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    change (0 : ℝ) ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
    exact ⟨by linarith [hℓ], by linarith [hℓ]⟩
  have hCfn : 0 ≤ Cf := le_trans (abs_nonneg (fib 0)) (hfibb 0 hCube0)
  have hδb : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N ℓ →
      |δ (x i)| ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| := by
    intro i x hx
    have hxi : x i ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff N ℓ x).mp hx i
    calc |δ (x i)| = |fib (x i) - Work.BoseFixB1S.boxM1 ℓ A w₁ / V| := by simp only [hδ]
      _ ≤ |fib (x i)| + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| := abs_sub _ _
      _ ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| :=
          add_le_add (hfibb (x i) hxi) (le_refl _)
  have hδAESM : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => δ (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := by
    intro i
    have h1 : MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X N => fib (x i))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) :=
      Submission.BoseGases.aem_comp_coord' i hfibaesm
    have h2 := h1.sub (MeasureTheory.aestronglyMeasurable_const :
      MeasureTheory.AEStronglyMeasurable
        (fun _ : Submission.BoseGases.X N => Work.BoseFixB1S.boxM1 ℓ A w₁ / V) _)
    have h3 : (fun x : Submission.BoseGases.X N => δ (x i))
        = (fun x : Submission.BoseGases.X N => fib (x i))
          - (fun _ : Submission.BoseGases.X N => Work.BoseFixB1S.boxM1 ℓ A w₁ / V) := by
      funext x
      simp only [hδ, Pi.sub_apply]
    rw [h3]
    exact h2
  -- ## component bounds and measurability
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  have hG : ∀ c : Finset (Fin N) × Finset (Fin N), Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.boxCompT V A c.1 c.2 Φ) :=
    fun c => Work.BoseFixB1S.goodState_boxCompT hℓ hVpos hAmeas hVeq hAc c.1 c.2 hΦG
  have hGb : ∀ c : Finset (Fin N) × Finset (Fin N), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.BoseFixB1S.boxCompT V A c.1 c.2 Φ x| ≤ C := by
    intro c
    obtain ⟨hm, C, hb⟩ := hG c
    exact ⟨max C 0, le_max_right _ _, fun x hx => le_trans (hb x hx) (le_max_left _ _)⟩
  set K : Finset (Fin N) × Finset (Fin N) → ℝ := fun c => Classical.choose (hGb c) with hK
  have hKnn : ∀ c : Finset (Fin N) × Finset (Fin N), 0 ≤ K c :=
    fun c => (Classical.choose_spec (hGb c)).1
  have hKb : ∀ (c : Finset (Fin N) × Finset (Fin N)) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N ℓ → |Work.BoseFixB1S.boxCompT V A c.1 c.2 Φ x| ≤ K c :=
    fun c x hx => (Classical.choose_spec (hGb c)).2 x hx
  have hKm : ∀ c : Finset (Fin N) × Finset (Fin N), Measurable (Work.BoseFixB1S.boxCompT V A c.1 c.2 Φ) :=
    fun c => (hG c).1
  -- ## the per-slot identity
  have hslot : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * δ (x i)
            * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)))
        = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            (((p.1.card : ℝ) - 1 - μ * V)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                    * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) := by
    intro i
    set Qs : Finset (Finset (Fin N) × Finset (Fin N)) :=
      (Work.BoseFixB1.disjPairs N).filter (fun q => i ∈ q.2) with hQs
    have hQ : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A i Φ x = ∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x :=
      fun x hx => hopQIndDecomp_g hℓ hVpos hAmeas hVeq hAc hΦm hΦb i x hx
    have hβ : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x
            - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)
          = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
              ((p.1.card : ℝ) - 1 - μ * V) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x :=
      fun x hx => hopBracketDecomp_g hℓ hVpos hAmeas hVeq hAc hΦm hΦb i x hx
    -- measurability of the `Q`-sum
    have hQm : Measurable (fun x : Submission.BoseGases.X N =>
        ∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) :=
      Finset.measurable_sum _ (fun q _ => hKm q)
    -- integrability of the `p`-summands
    have hB : ∀ p ∈ Work.BoseFixB1S.hopPairSet i, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          ((∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i)) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
      intro p hp
      refine Work.BoseFixB1S.integrableOn_abox_of_bound_aesm
        (C := (∑ q ∈ Qs, K q) * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p) hℓ ?_ ?_
      · exact (hQm.aestronglyMeasurable.mul (hδAESM i)).mul (hKm p).aestronglyMeasurable
      · intro x hx
        have h1 : |∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x| ≤ ∑ q ∈ Qs, K q :=
          le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun q _ => hKb q x hx))
        have h2 : 0 ≤ ∑ q ∈ Qs, K q := Finset.sum_nonneg (fun q _ => hKnn q)
        have h3 : 0 ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| :=
          add_nonneg hCfn (abs_nonneg _)
        calc |((∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i)) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x|
            = |∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x| * |δ (x i)|
                * |Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x| := by rw [abs_mul, abs_mul]
          _ ≤ (∑ q ∈ Qs, K q) * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p := by
              refine mul_le_mul (mul_le_mul h1 (hδb i x hx) (abs_nonneg _) h2)
                (hKb p x hx) (abs_nonneg _) (mul_nonneg h2 h3)
    -- the inner distribution, and the collapse
    have hInner1 : ∀ p ∈ Work.BoseFixB1S.hopPairSet i,
        (∫ x in Submission.BoseGases.abox N ℓ,
            ((∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i))
              * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x)
          = ∑ q ∈ Qs, ∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x * δ (x i) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x := by
      intro p hp
      have hsum_eq : (∫ x in Submission.BoseGases.abox N ℓ,
            ((∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i)) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x)
          = ∫ x in Submission.BoseGases.abox N ℓ,
              (∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x * δ (x i))
                * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x := by
        refine MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable N ℓ) (fun x _ => ?_)
        rw [Finset.sum_mul]
      rw [hsum_eq]
      refine Work.BoseFixB1S.abox_integral_sum_mul Qs
        (fun q x => Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x * δ (x i))
        (fun x => Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ?_
      intro q hq
      refine Work.BoseFixB1S.integrableOn_abox_of_bound_aesm
        (C := K q * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p) hℓ ?_ ?_
      · exact ((hKm q).aestronglyMeasurable.mul (hδAESM i)).mul (hKm p).aestronglyMeasurable
      · intro x hx
        have h3 : 0 ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V| :=
          add_nonneg hCfn (abs_nonneg _)
        calc |(Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x * δ (x i)) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x|
            = |Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x| * |δ (x i)| * |Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x| := by
              rw [abs_mul, abs_mul]
          _ ≤ K q * (Cf + |Work.BoseFixB1S.boxM1 ℓ A w₁ / V|) * K p :=
              mul_le_mul (mul_le_mul (hKb q x hx) (hδb i x hx) (abs_nonneg _) (hKnn q))
                (hKb p x hx) (abs_nonneg _) (mul_nonneg (hKnn q) h3)
    have hInner2 : ∀ p ∈ Work.BoseFixB1S.hopPairSet i,
        (∑ q ∈ Qs, ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x * δ (x i) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x)
          = ∫ x in Submission.BoseGases.abox N ℓ,
              Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x := by
      intro p hp
      have hpd : p ∈ Work.BoseFixB1.disjPairs N := (Work.BoseFixB1S.mem_hopPairSet.mp hp).1
      have hpi : i ∈ p.1 := (Work.BoseFixB1S.mem_hopPairSet.mp hp).2
      exact Work.BoseFixB1S.hopCollapseGen (ℓ := ℓ) (volA := V) (A := A) (g := δ) (Φ := Φ)
        hpd hpi
        (fun S T S' T' hST hST' j hj hdif => horth i S T S' T' hST hST' j hj hdif)
    calc (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * δ (x i)
            * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i)
              * (∑ p ∈ Work.BoseFixB1S.hopPairSet i,
                  ((p.1.card : ℝ) - 1 - μ * V) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) := by
          refine MeasureTheory.setIntegral_congr_fun
            (Submission.BoseGases.abox_measurable N ℓ) (fun x hx => ?_)
          rw [hQ x hx, hβ x hx]
      _ = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            ((p.1.card : ℝ) - 1 - μ * V)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  ((∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i))
                    * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x :=
          Work.BoseFixB1S.abox_integral_mul_finset_sum (Work.BoseFixB1S.hopPairSet i)
            (fun x => (∑ q ∈ Qs, Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) * δ (x i))
            (fun p => (p.1.card : ℝ) - 1 - μ * V)
            (fun p x => Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) hB
      _ = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            ((p.1.card : ℝ) - 1 - μ * V)
              * ∑ q ∈ Qs, ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x * δ (x i) * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [hInner1 p hp]
      _ = ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            ((p.1.card : ℝ) - 1 - μ * V)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                    * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [hInner2 p hp]
  -- ## the assembly
  have hVne : V ≠ 0 := ne_of_gt hVpos
  calc (V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ
        - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x)))
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) * δ (x i)
            * ((Work.UBBInputs8.boxPInd V A i (Work.BoseFixB1.rungF V A Φ) x)
                - (1 + μ * V) * (Work.UBBInputs8.boxPInd V A i Φ x)) := by
        rw [hcent]
        have harith : V / 2 * (2 / V) = 1 := by field_simp
        rw [← mul_assoc, harith, one_mul]
    _ = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (((p.1.card : ℝ) - 1 - μ * V)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * δ (x i)
                  * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) :=
        Finset.sum_congr rfl (fun i _ => hslot i)

/-! ## 3. The target -/

theorem measHopExpansionFibCorr {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
      {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
      (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb),
      (Work.SmallBoxSliding.boxMass ℓ d u / 2) *
        (Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          - 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x)))
      = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
          (((p.1.card : ℝ) - 1 - μ * Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) (p.1.erase i) (insert i p.2) Φ x
                  * Submission.BoseGases.w1Fibre ℓ
                      (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
                  * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) p.1 p.2 Φ x) := by
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦm Cb hΦb
  -- ## the regularity of the localised fibre
  obtain ⟨-, ⟨hFibAesm, Cf, hCfnn, hCfb⟩⟩ :=
    Work.BoseFixB1.q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad h (M := M) hM
      hℓ hd hR hRχ u
  have hFibAesm' : MeasureTheory.AEStronglyMeasurable
      (Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    simpa only [Work.BoseFixB1.q1Fib1] using hFibAesm
  have hCfb' : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z| ≤ Cf :=
    fun z _ => by simpa only [Work.BoseFixB1.q1Fib1] using hCfb z
  -- ## box data
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- ## the centred identity at the measurable state
  have hcent := boxCrossCentred_g (v := v) (R0 := R0) (μ := μ)
    hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦm hΦb
  -- ## the weighted orthogonality at the centred fibre weight
  have horth : ∀ (i : Fin N) (S T S' T' : Finset (Fin N)), Disjoint S T → Disjoint S' T' →
      ∀ j : Fin N, j ≠ i →
        Work.BoseFixB1S.orthSlotType S T j ≠ Work.BoseFixB1S.orthSlotType S' T' j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) S T Φ x
          * (Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)
              - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                / Work.SmallBoxSliding.boxMass ℓ d u)
          * Work.BoseFixB1S.boxCompT (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) S' T' Φ x) = 0 := by
    intro i S T S' T' hST hST' j hj hdif
    have hδaesm : MeasureTheory.AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
            - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u)
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) :=
      hFibAesm'.sub aestronglyMeasurable_const
    have hδb : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
            - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / Work.SmallBoxSliding.boxMass ℓ d u|
          ≤ Cf + |Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u| :=
      fun z hz => le_trans (abs_sub _ _) (add_le_add (hCfb' z hz) le_rfl)
    exact hopCompTWeightedOrthAe_g (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (g := fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
          - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            / Work.SmallBoxSliding.boxMass ℓ d u)
      hℓ hvol hAmeas hVeq hAc hδaesm
      (Bg := Cf + |Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        / Work.SmallBoxSliding.boxMass ℓ d u|) hδb hj hST hST' hdif hΦm hΦb hΦm hΦb
  -- ## the expansion core
  have hexp := expansionCore_g (ℓ := ℓ) (V := Work.SmallBoxSliding.boxMass ℓ d u) (μ := μ)
    (A := Submission.BoseGases.dlBox ℓ d u)
    (w₁ := Submission.BoseGases.wSmall1Pair h M ℓ d u) (Φ := Φ)
    (fib := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
    (Cf := Cf) hℓ hvol hAmeas hVeq hAc hΦm hΦb hFibAesm' hCfb' hcent horth
  rw [hexp]
  -- ## the only difference is the centring, which vanishes edge by edge
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p hp => ?_))
  rw [integral_child_sub_kappa_g (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (κ := Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        / Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u)
      (fib := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Cf := Cf) hℓ hvol hAmeas hVeq hAc hFibAesm' hCfb' hΦm hΦb hp]

end Work.BoseFixB1.SectorAux
