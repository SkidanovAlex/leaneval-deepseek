import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_sectorPieceProj
import Submission.Work.BoseFixB1M.boxMuSum
import Submission.Work.BoseFixB1N.boxFragsIntegrable_dlBox
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.fibreAeTransfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorPiece

open MeasureTheory
open scoped Real BigOperators ENNReal

/-! ## The one-slot integrability bricks

Every integrand appearing in the `μ`-part of the box words at a sector piece is of the shape
`G x · fib (x i)`, where `fib` is the one-slot fibre of the localised kernel and `G` is a
bounded measurable function of the configuration.  The following lemma turns the *fibre* inputs
(measurability on the one-particle cube, boundedness there) plus the *multiplier* inputs
(a.e. strong measurability and boundedness on the compact box) into integrability on the box.

The only measure-theoretic content is that the `i`-th coordinate is quasi-measure-preserving from
`volume.restrict (abox N ℓ)` to `volume.restrict (acube ℓ)`
(`Work.BoseFixB1S.quasiMeasurePreserving_coord_abox`), so a.e. strong measurability of the fibre
transports to its `i`-th coordinate pull-back. -/
private theorem integrableOn_mul_fibre {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable fib
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)))
    {Cf : ℝ} (hfb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {G : Submission.BoseGases.X N → ℝ}
    (hGm : MeasureTheory.AEStronglyMeasurable G
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)))
    {CG : ℝ} (hGb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |G x| ≤ CG)
    (i : Fin N) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => G x * fib (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  have hfib_i : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => fib (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    hfm.comp_quasiMeasurePreserving (Work.BoseFixB1S.quasiMeasurePreserving_coord_abox i)
  refine MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) (hGm.mul hfib_i) (|CG| * |Cf|) ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hGb x hx) (le_abs_self CG))
    (le_trans (hfb (x i) (hx i)) (le_abs_self Cf)) (abs_nonneg _) (abs_nonneg _)

/-- The `Q`-reading of a state bounded by `C` on the box is bounded by `2C` there, *without* any
positivity assumption on the volume `volA` of the box (contrast
`Work.BoseFixB1N.abs_boxQInd_le`, which assumes `0 < volA`).

When `volA = 0` division by `volA` kills the projection, so `Q_iΨ = 1_A(x_i)·Ψ`; otherwise the
box projection bound `Work.BoseFixB1S.abs_boxPInd_le` applies. -/
private theorem abs_boxQInd_le_of_bound {N : ℕ} {ℓ volA C : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hC0 : 0 ≤ C)
    (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * C := by
  intro x hx
  by_cases hV0 : volA = 0
  · have hP0 : Work.UBBInputs8.boxPInd volA A i Ψ x = 0 := by
      simp only [Work.UBBInputs8.boxPInd, hV0, div_zero, zero_mul]
    rw [Work.UBBInputs8.boxQInd, hP0, sub_zero]
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases h : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * C :=
          mul_le_mul hind (hC x hx) (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
      _ ≤ 2 * C := by linarith
  · have hVpos : 0 < volA :=
      lt_of_le_of_ne (by rw [hvolA]; exact ENNReal.toReal_nonneg) (Ne.symm hV0)
    exact Work.BoseFixB1N.abs_boxQInd_le hℓ hVpos hA hvolA hAc i hC x hx

/-- The `P`-reading of a state bounded by `C` on the box is bounded by `C` there, again without a
positivity assumption on `volA`: if `volA = 0` the projection vanishes. -/
private theorem abs_boxPInd_le_of_bound {N : ℕ} {ℓ volA C : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hC0 : 0 ≤ C)
    (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Ψ x| ≤ C := by
  intro x hx
  by_cases hV0 : volA = 0
  · simp only [Work.UBBInputs8.boxPInd, hV0, div_zero, zero_mul, abs_zero]
    exact hC0
  · have hVpos : 0 < volA :=
      lt_of_le_of_ne (by rw [hvolA]; exact ENNReal.toReal_nonneg) (Ne.symm hV0)
    exact Work.BoseFixB1S.abs_boxPInd_le hℓ hVpos hA hvolA hAc i hC x hx

theorem boxMuSum_sectorPiece {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} (k : ℕ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    (∑ i : Fin N, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) i)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ x) ^ 2
            * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)) := by
  classical
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  set W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    Submission.BoseGases.wSmall1Pair h M ℓ d u with hWdef
  set sP : Submission.BoseGases.X N → ℝ :=
    Work.FockBridge.sectorPiece A k Φ with hsPdef
  -- the fibre constant
  set Cf : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
    (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        / Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * _root_.BoseGases.a v))
    with hCfdef
  -- the fibre facts
  have hfib_meas : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.w1Fibre ℓ W z)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)) := by
    have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    have h0 := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      hg0.aemeasurable
    simpa only [Submission.BoseGases.w1Fibre, hWdef, Submission.BoseGases.wSmall1Pair] using h0
  have hfib_zero : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A →
      Submission.BoseGases.w1Fibre ℓ W z = 0 := by
    intro z hz
    have hchi : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
      by_contra hne
      exact hz (by
        rw [hAdef]
        exact Work.BoseFixB1S.chiSmallB_support_subset_dlBox hM hℓ hd u
          (Function.mem_support.mpr hne))
    have hzero : ∀ y : EuclideanSpace ℝ (Fin 3), W z y = 0 := by
      intro y
      simp only [hWdef, Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hchi,
        zero_mul]
    rw [Submission.BoseGases.w1Fibre]
    simp only [hzero]
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y _ => rfl)
  have hfib_le : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.w1Fibre ℓ W z| ≤ Cf := by
    intro z
    have h0 := Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
    rw [hCfdef]
    simpa only [Submission.BoseGases.w1Fibre, hWdef, Submission.BoseGases.wSmall1Pair] using h0
  -- structural facts about the small box
  have hA : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : V = (MeasureTheory.volume A).toReal := by
    rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- `Φ` is bounded on the compact box
  obtain ⟨C, hCbd⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hCabs : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hCbd x hx
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Φ 0))
    (hCabs 0 (Submission.BoseGases.zero_mem_abox (N := N) (ℓ := ℓ) hℓ.le))
  have hΦm : Measurable Φ := hΦc.measurable
  have hsPm : Measurable sP := by
    rw [hsPdef, Work.FockBridge.sectorPiece]
    exact hΦm.indicator (Work.FockBridge.sectorSet_measurable A hA k)
  have hsPb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |sP x| ≤ C := by
    intro x hx
    rw [hsPdef, Work.FockBridge.sectorPiece]
    by_cases hxs : x ∈ Work.FockBridge.sectorSet A k
    · rw [Set.indicator_of_mem hxs]; exact hCabs x hx
    · rw [Set.indicator_of_notMem hxs, abs_zero]; exact hC0
  -- bounds of the box readings of the sector piece
  have hPbound : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i sP x| ≤ C :=
    fun i => abs_boxPInd_le_of_bound hℓ hA hvolA hAc hC0 i hsPb
  have hQbound : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i sP x| ≤ 2 * C :=
    fun i => abs_boxQInd_le_of_bound hℓ hA hvolA hAc hC0 i hsPb
  -- the three `μ`-integrabilities at the sector piece
  have hIntP : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd V A i sP x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro i
    refine integrableOn_mul_fibre hℓ hfib_meas (fun z _ => hfib_le z)
      (G := fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxPInd V A i sP x) ^ 2)
      ((Work.BoseFixB1S.measurable_boxPInd V A hA i hsPm).pow_const 2).aestronglyMeasurable
      (CG := C ^ 2) (fun x hx => ?_) i
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hPbound i x hx) 2
  have hIntQP : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i sP x) * (Work.UBBInputs8.boxPInd V A i sP x)
          * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro i
    refine integrableOn_mul_fibre hℓ hfib_meas (fun z _ => hfib_le z)
      (G := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i sP x) * (Work.UBBInputs8.boxPInd V A i sP x))
      (((Work.BoseFixB1N.measurable_boxQInd V A hA i hsPm).mul
        (Work.BoseFixB1S.measurable_boxPInd V A hA i hsPm))).aestronglyMeasurable
      (CG := (2 * C) * C) (fun x hx => ?_) i
    rw [abs_mul]
    exact mul_le_mul (hQbound i x hx) (hPbound i x hx) (abs_nonneg _)
      (mul_nonneg (by norm_num) hC0)
  have hIntQ : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i sP x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro i
    refine integrableOn_mul_fibre hℓ hfib_meas (fun z _ => hfib_le z)
      (G := fun x : Submission.BoseGases.X N => (Work.UBBInputs8.boxQInd V A i sP x) ^ 2)
      ((Work.BoseFixB1N.measurable_boxQInd V A hA i hsPm).pow_const 2).aestronglyMeasurable
      (CG := (2 * C) ^ 2) (fun x hx => ?_) i
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hQbound i x hx) 2
  -- integrability of the `boxMuPhi` integrands
  have hIntPhi : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (sP x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro i
    refine integrableOn_mul_fibre hℓ hfib_meas (fun z _ => hfib_le z)
      (G := fun x : Submission.BoseGases.X N => (sP x) ^ 2)
      (hsPm.pow_const 2).aestronglyMeasurable (CG := C ^ 2) (fun x hx => ?_) i
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsPb x hx) 2
  -- the per-slot `μ`-identity at the sector piece
  have hslot : ∀ i : Fin N,
      Work.BoseFixB1S.boxMuP V ℓ A W sP i
        + 2 * Work.BoseFixB1S.boxMuQP V ℓ A W sP i
        + Work.BoseFixB1S.boxMuQ V ℓ A W sP i
      = Work.BoseFixB1S.boxMuPhi (N := N) ℓ W sP i :=
    fun i => Work.BoseFixB1M.boxMu_slot (ℓ := ℓ) (volA := V) (A := A) (w1 := W)
      hfib_zero i (hIntP i) (hIntQP i) (hIntQ i)
  calc
    (∑ i : Fin N, Work.BoseFixB1S.boxMuP V ℓ A W sP i)
        + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP V ℓ A W sP i)
        + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ V ℓ A W sP i)
        = ∑ i : Fin N, (Work.BoseFixB1S.boxMuP V ℓ A W sP i
            + 2 * Work.BoseFixB1S.boxMuQP V ℓ A W sP i
            + Work.BoseFixB1S.boxMuQ V ℓ A W sP i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ W sP i :=
          Finset.sum_congr rfl (fun i _ => hslot i)
      _ = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (sP x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i) := by
          simp only [Work.BoseFixB1S.boxMuPhi]
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            (∑ i : Fin N, (sP x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i)) := by
          rw [← integral_finsetSum (Finset.univ : Finset (Fin N))
            (fun i _ => by simpa [MeasureTheory.IntegrableOn] using hIntPhi i)]
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            (sP x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ W (x i)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.mul_sum]

end Work.BoseFixB1.SectorPiece
