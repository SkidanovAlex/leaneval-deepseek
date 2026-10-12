import ChallengeDeps
import Submission.Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1
import Submission.Work.BoseFixB1.boxPInd_boxQInd_self
import Submission.Work.BoseFixB1.boxPInd_rungF_pointwise
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxCrossCentredB1S`

A cycle-free copy of `Work.BoseFixB1.boxCrossPart_centred` (same statement and proof, namespace
`Work.BoseFixB1S`, renamed `boxCrossPartCentredB1S`).  The original module imports
`Work.BoseFixB1S.boxPInd_QInd_sum_eq_zero`, which imports `Work.BoseFixB1.boxQSum_ge_a0Main_add_A2`,
which imports the target module `Work.BoseFixB1S.boxCrossHoppingSharpLow` of this line; importing
the original from the target module would therefore close an import cycle.  That import is unused
in the original file (its proof uses only `boxCrossPart_sub_twoMuP_eq_operatorB1`,
`boxPInd_rungF_pointwise`, `pIndOrth`, `boxPIndSelfAdjoint`, `boxPInd_self_idem`,
`boxPInd_boxQInd_self`, `measurable_boxQInd`, `boxM1Info`, `BoxPIndFlat`), so dropping it is
faithful; every other import is kept verbatim.

The header of the original file, verbatim:
-/

/-
# `Work.BoseFixB1.boxCrossPart_centred` — the fibre-centred form of the box cross term

FS `eq:Q1n0` for the **cross term** of the box-projected pair block, with the one-body fibre
`fib₁ = w1Fibre ℓ w₁` *centred* by its box mean `κ = M₁/V` (`M₁ = boxM1 ℓ (dlBox ℓ d u) w₁`,
`V = boxMass ℓ d u`): the sliding-box cross part of the localised `g₀`-kernel
`w₁ = wSmall1Pair h M ℓ d u` satisfies

  `boxCrossPart − 2μ·P = (2/V)·Σᵢ ∫ (QᵢΦ)·(fib₁(xᵢ) − κ)·(Pᵢ(rungF) − (1+μV)·PᵢΦ)`

with `P = Σᵢ∫(QᵢΦ)·fib₁(xᵢ)·(PᵢΦ)`, `Pᵢ = boxPInd V A i`, `Qᵢ = boxQInd V A i` and
`rungF V A Φ = Σ_j P_jΦ` (`n₀`).

## Proof

The previous lemma `boxCrossPart_sub_twoMuP_eq_operatorB1` computes the same left-hand side as

  `(2/V)·Σᵢ ∫ (QᵢΦ)·fib₁(xᵢ)·(Σ_j P_j(PᵢΦ) − (1+μV)·PᵢΦ)`,

and `Work.BoseFixB1.boxPInd_rungF_pointwise` identifies `Σ_j P_j(PᵢΦ) = Pᵢ(rungF)` on the box
(slot-`i` linearity of `Pᵢ` plus the two-slot commutation `PᵢP_j = P_jPᵢ`, `j ≠ i`).  So it
remains to replace `fib₁` by `fib₁ − κ`; pointwise the two differ by `−κ·(QᵢΦ)·(Pᵢ(rungF) −
(1+μV)PᵢΦ)`, and the remaining sum vanishes per slot because `Qᵢ` is `L²`-orthogonal to the
range of the self-adjoint projection `Pᵢ`:

* `∫(QᵢΦ)·(Pᵢ(rungF)) = ∫(Pᵢ(QᵢΦ))·(rungF) = 0` — self-adjointness of `Pᵢ`
  (`Work.BoseFixB1S.boxPIndSelfAdjoint`) together with `PᵢQᵢ = 0`
  (`Work.BoseFixB1.boxPInd_boxQInd_self`);
* `∫(QᵢΦ)·(PᵢΦ) = 0` — the corpus orthogonality `Work.BoseSplit.pIndOrth`.

All integrability side conditions come from the boundedness of the factors on the compact box
(`Work.BoseFixB1S.integrableOn_mul_of_bound`, `Work.BoseFixB1.integrableOn_abox_slot_mul`).
-/
namespace Work.BoseFixB1S

open MeasureTheory

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem boxCrossPartCentredB1S {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
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
  -- ## bounds for the state
  obtain ⟨C₀, hC₀⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  set CΦ : ℝ := max C₀ 0 with hCΦdef
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hC₀ x hx) (le_max_left _ _)
  have hPb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k Φ x| ≤ CΦ :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hVpos hAmeas hVeq' hAc k hΦb
  have hQb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A k Φ x| ≤ 2 * CΦ := by
    intro k x hx
    have hP := hPb k x hx
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x k)| ≤ 1 := by
      by_cases hk : x k ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hk]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x k) * Φ x| ≤ CΦ := by
      rw [abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x k)| * |Φ x| ≤ 1 * CΦ :=
            mul_le_mul hind (hΦb x hx) (abs_nonneg _) (by norm_num)
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
    fun k => Work.SlotWord.measurable_boxQInd V A hAmeas k hΦc.measurable
  have hPm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxPInd V A k Φ) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd V A hAmeas k hΦc.measurable
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
      rw [Work.BoseFixB1.boxPInd_boxQInd_self (volA := V) (A := A) hℓ hVpos hAmeas hVeq' hAc k hΦc x hx,
        mul_zero]
    rw [MeasureTheory.integral_congr_ae hzero]
    simp
  have hZ2 : ∀ k : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A k Φ x * Work.UBBInputs8.boxPInd V A k Φ x) = 0 := by
    intro k
    have horth := Work.BoseSplit.pIndOrth (N := N) (ℓ := ℓ) (volA := V) hℓ hVpos hAmeas
      hVeq' hAc k hΦc
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
    have h2 := Work.BoseFixB1.boxPInd_rungF_pointwise (volA := V) (A := A) hℓ hVpos hAmeas hVeq' hAc k hΦc x hx
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
      (Work.BoseFixB1.boxCrossPart_sub_twoMuP_eq_operatorB1 (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
        (M := M) hM (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol (N := N) (Φ := Φ) hΦc)
  rw [hprev]
  congr 1
  exact hAB.trans hCen.symm

end Work.BoseFixB1S
