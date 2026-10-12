import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.RungDefs
import Submission.Work.BoseFixB1.amgmSlotSumMeas
import Submission.Work.BoseFixB1.boxFlatCountZeroAe
import Submission.Work.BoseFixB1.boxPIndFibreMassB1
import Submission.Work.BoseFixB1.boxQIndFibreCountB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxQ1CrossSqrtB1`

FS's `√n₀`-completion for the `Q₁`-cross line of the localised small-box word
(`thm:smallbox` at the sliding box): with `V = |B(u)|`, `A = dlBox ℓ d u`,
`S = boxFlatCount`, `n₊ = boxQCount`, `M₁ = boxM1` (the fibre mass) and `fib₁` the fibre of
`wSmall1Pair h M ℓ d u`,

    2t·Σᵢ∫ (QᵢΦ)(PᵢΦ)·fib₁(xᵢ) ≥ −¼t²M₁ − K a(v)·(S/V)·(S + n₊) .

**Proof structure.**  The `P²`-mass at the fibre weight is `Σᵢ∫(PᵢΦ)² fib₁(xᵢ) = (M₁/V)·S`
(`boxPIndFibreMassB1`), so the per-slot completion of squares
`0 ≤ ∫ (V·t·PᵢΦ + 4S·QᵢΦ)² fib₁(xᵢ)` — equivalently the AM–GM at `A = 4S/V`, `W = M₁`
(`amgmSlotSumMeas`) — gives

    2t·Σᵢ∫(QᵢΦ)(PᵢΦ)fib₁ ≥ −¼t²M₁ − (4S/V)·Σᵢ∫(QᵢΦ)²fib₁ ,

and the `Q²`-line is bounded by `Kfib·n₊` (`boxQIndFibreCountB1`).  Paying `(4S/V)·Kfib·n₊` by
`K a(v)(S/V)(S + n₊)` with `K = 4·KfibConst M` (where `Kfib = KfibConst M · a(v)`) is the
arithmetic of `payArith`; the degenerate case `S = 0` is handled separately, where the cross term
vanishes because every `PᵢΦ` is a.e. `0` (`boxFlatCountZeroAe`) while `M₁ ≥ 0`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The `M`-dependent constant of the fibre bound, and `a(v) ≥ 0` -/

/-- The `M`-dependent constant of `Work.BoseFixB1.Kfib`, defined so that
`Kfib v M = KfibConst M * a v`. -/
noncomputable def KfibConst (M : ℕ) : ℝ :=
  (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
    * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi))

lemma KfibConst_nonneg (M : ℕ) : 0 ≤ KfibConst M := by
  have h1 : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have h2 : 0 ≤ Submission.BoseGases.chiSmallDecay M := Submission.BoseGases.chiSmallDecay_nonneg M
  have h3 : 0 < Work.SmallBoxSliding.smallConvLower M := Work.SmallBoxSliding.smallConvLower_pos M
  unfold KfibConst
  positivity

lemma Kfib_eq_KfibConst_mul_a (v : EuclideanSpace ℝ (Fin 3) → ℝ) (M : ℕ) :
    Kfib (v := v) M = KfibConst M * _root_.BoseGases.a v := by
  rw [Kfib, KfibConst]
  ring

/-- The scattering length is nonnegative: `8π a v = ∫|g₀|`. -/
lemma a_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ} (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) :
    0 ≤ _root_.BoseGases.a v := by
  have h1 : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z| :=
    integral_nonneg (fun z => abs_nonneg _)
  have h2 : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
      = 8 * Real.pi * _root_.BoseGases.a v :=
    Submission.BoseGases.g0_abs_integral hR0 hv hvrad hv_supp h
  have h3 : 0 ≤ 8 * Real.pi * _root_.BoseGases.a v := by rw [← h2]; exact h1
  nlinarith [Real.pi_pos]

/-! ## 1. Nonnegativity of the counts and of the fibre mass -/

lemma boxFlatCount_nonneg {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {Φ : Submission.BoseGases.X N → ℝ} :
    0 ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
  rw [Work.BoseFixB1S.boxFlatCount]
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))

lemma boxQCount_nonneg {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {Φ : Submission.BoseGases.X N → ℝ} :
    0 ≤ Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  rw [Work.BoseFixB1S.boxQCount]
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))

/-- The fibre mass `M₁ = ∫_A fib₁ ≥ 0` for a nonnegative fibre. -/
lemma boxM1_nonneg {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {w1 : E3 → E3 → ℝ}
    (h : ∀ z, 0 ≤ Submission.BoseGases.w1Fibre ℓ w1 z) :
    0 ≤ Work.BoseFixB1S.boxM1 ℓ A w1 := by
  rw [Work.BoseFixB1S.boxM1]
  exact integral_nonneg (fun z => h z)

/-! ## 2. The payment arithmetic -/

/-- The `Q²`-line's coefficient `4S/V` times the fibre mass bound `Kfib = CM·a(v)` is paid by
`K·a(v)·(S/V)·(S + n₊)` as soon as `K ≥ 4·CM`, `S, n₊ ≥ 0` and `a(v) ≥ 0`. -/
private lemma payArith {K CM av S QN V Kfib1 : ℝ} (hV : 0 < V) (hCM : 0 ≤ CM) (hav : 0 ≤ av)
    (hS : 0 ≤ S) (hQN : 0 ≤ QN) (hKfib1 : Kfib1 = CM * av) (hK : 4 * CM ≤ K) :
    (4 * S / V) * (Kfib1 * QN) ≤ K * av * (S / V) * (S + QN) := by
  have hVinv : 0 ≤ V⁻¹ := inv_nonneg.mpr hV.le
  have haux : (4 * S) * (Kfib1 * QN) ≤ (K * av * S) * (S + QN) := by
    rw [hKfib1]
    calc (4 * S) * ((CM * av) * QN) = (4 * CM) * (av * S) * QN := by ring
      _ ≤ (4 * CM) * (av * S) * (S + QN) := by
        refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hS) ?_
        exact mul_nonneg (by linarith) (mul_nonneg hav hS)
      _ ≤ K * (av * S) * (S + QN) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact mul_le_mul_of_nonneg_right hK (mul_nonneg hav hS)
      _ = (K * av * S) * (S + QN) := by ring
  calc (4 * S / V) * (Kfib1 * QN) = ((4 * S) * (Kfib1 * QN)) * V⁻¹ := by ring
    _ ≤ ((K * av * S) * (S + QN)) * V⁻¹ := mul_le_mul_of_nonneg_right haux hVinv
    _ = K * av * (S / V) * (S + QN) := by ring

/-! ## 3. The nondegenerate case: AM–GM + count bound + payment -/

/-- Assembly of the nondegenerate case: the completed square (`hAM`) and the `Q²`-count bound
(`hQcnt`) give the target bound with `K = 4·KfibConst M`. -/
private theorem amgmCombine {v : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} {t : ℝ}
    {X0 Qsum M1 S QN V : ℝ} (hV : 0 < V) (hSnn : 0 ≤ S) (hQNnn : 0 ≤ QN) (hM1nn : 0 ≤ M1)
    (hav : 0 ≤ _root_.BoseGases.a v)
    (hAM : 2 * t * X0 ≥ - (1 / 4) * t ^ 2 * M1 - (4 * S / V) * Qsum)
    (hQcnt : Qsum ≤ Kfib (v := v) M * QN) :
    2 * t * X0 ≥ - (1 / 4) * t ^ 2 * M1
      - (max (4 * KfibConst M) 0) * (_root_.BoseGases.a v) * (S / V) * (S + QN) := by
  have hQm : (4 * S / V) * Qsum ≤ (4 * S / V) * (Kfib (v := v) M * QN) :=
    mul_le_mul_of_nonneg_left hQcnt (div_nonneg (by linarith) hV.le)
  have hpay := payArith (K := max (4 * KfibConst M) 0) (CM := KfibConst M)
    (av := _root_.BoseGases.a v) (S := S) (QN := QN) (V := V)
    (Kfib1 := Kfib (v := v) M) hV (KfibConst_nonneg M) hav hSnn hQNnn
    (Kfib_eq_KfibConst_mul_a v M) (le_max_left _ _)
  linarith

/-! ## 4. The degenerate case `S = 0` -/

/-- Assembly of the degenerate case: if every `PᵢΦ` vanishes a.e. then the cross term is `0`,
while the right-hand side is `≤ 0` (the `(S/n₊)`-credit vanishes because `S = 0`). -/
private theorem crossDeg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} {t : ℝ}
    {ℓ V : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {f : E3 → ℝ}
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} {S QN M1 : ℝ}
    (hS0 : S = 0) (hM1nn : 0 ≤ M1)
    (hvan : ∀ i : Fin N,
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd V A i Φ x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0) :
    2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x) * f (x i))
      ≥ - (1 / 4) * t ^ 2 * M1
        - (max (4 * KfibConst M) 0) * (_root_.BoseGases.a v) * (S / V) * (S + QN) := by
  have hX : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x) * f (x i))
      = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h0 : (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x) * f (x i))
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
      filter_upwards [hvan i] with x hx
      simp [hx]
    rw [MeasureTheory.integral_congr_ae h0]
    simp
  subst hS0
  rw [hX, mul_zero]
  have hzero : (max (4 * KfibConst M) 0) * _root_.BoseGases.a v * (0 / V) * (0 + QN) = 0 := by
    ring
  rw [hzero]
  nlinarith [hM1nn, sq_nonneg t]

/-! ## 5. The target -/

theorem boxQ1CrossSqrtB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {t : ℝ} (ht : 0 ≤ t),
        2 * t * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * (Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
        ≥ - (1 / 4) * t ^ 2
            * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u))
          - K * (_root_.BoseGases.a v)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ
                + Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ) := by
  classical
  refine ⟨max (4 * KfibConst M) 0, le_max_right _ _, ?_⟩
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦc t ht
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  set f : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z => Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
    with hfdef
  set S : ℝ := Work.BoseFixB1S.boxFlatCount V ℓ A Φ with hSdef
  set QN : ℝ := Work.BoseFixB1S.boxQCount V ℓ A Φ with hQNdef
  set M1 : ℝ := Work.BoseFixB1S.boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u)
    with hM1def
  -- basic facts about the sliding box
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hVreal : V = (MeasureTheory.volume A).toReal := by
    rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- the fibre facts
  have hfval : ∀ z : EuclideanSpace ℝ (Fin 3), f z
      = Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => by rw [hfdef]
  have hfnn : ∀ z : EuclideanSpace ℝ (Fin 3), 0 ≤ f z := fun z => by
    rw [hfval z]
    exact q1cw1_w1Fibre_nonneg hv_supp hR0 hv hvrad h u z
  have hfb : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ Kfib (v := v) M := by
    intro z _
    rw [hfval z]
    exact q1cw1_w1Fibre_abs_le hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u z
  have hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have h1 := aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
    rw [hfdef]
    simpa only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using h1
  have hKfib0 : 0 ≤ Kfib (v := v) M :=
    q1cw1_Kfib_nonneg hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u
  have hav : 0 ≤ _root_.BoseGases.a v := a_nonneg (v := v) hR0 hv hvrad hv_supp h
  -- nonnegativity of the three counts/masses
  have hSnn : 0 ≤ S := by rw [hSdef]; exact boxFlatCount_nonneg
  have hQNnn : 0 ≤ QN := by rw [hQNdef]; exact boxQCount_nonneg
  have hM1nn : 0 ≤ M1 := by
    rw [hM1def]
    exact boxM1_nonneg (fun z => q1cw1_w1Fibre_nonneg hv_supp hR0 hv hvrad h u z)
  have hvan : S = 0 → ∀ i : Fin N,
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd V A i Φ x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := fun h0 =>
    boxFlatCountZeroAe hℓ hvol hAmeas (by rw [hVreal, MeasureTheory.Measure.real_def]) hAc hΦc h0
  by_cases hS0 : S = 0
  · exact crossDeg (v := v) (M := M) (t := t) (V := V) (A := A) (f := f)
      (N := N) (Φ := Φ) (QN := QN) (M1 := M1) hS0 hM1nn (hvan hS0)
  · -- nondegenerate case: the AM-GM at `A = 4S/V`, `W = M1`
    have hSpos : 0 < S := lt_of_le_of_ne hSnn (Ne.symm hS0)
    have hApos : 0 < 4 * S / V := div_pos (by linarith) (by rw [hVdef]; exact hvol)
    -- the `P²`-mass identity: `Σᵢ∫(PᵢΦ)² fib₁ = (M₁/V)·S`
    have hPmass : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * f (x i)) = (M1 / V) * S := by
      rw [hSdef, hM1def, hVdef, hAdef, hfdef]
      exact boxPIndFibreMassB1 hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦc
    -- the `Q²`-count bound
    have hQcnt : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * f (x i)) ≤ Kfib (v := v) M * QN := by
      rw [hQNdef, hVdef, hAdef, hfdef]
      exact boxQIndFibreCountB1 hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦc
    -- sup bound of `Φ` on the big box
    obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
    have hCΦ0 : 0 ≤ CΦ :=
      le_trans (norm_nonneg (Φ 0)) (hCΦ 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
    have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ := fun x hx => by
      simpa [Real.norm_eq_abs] using hCΦ x hx
    -- measurability and box bounds of the projections
    have hPm : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable (Work.UBBInputs8.boxPInd V A i Φ)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := fun i =>
      (Work.BoseFixB1S.measurable_boxPInd V A hAmeas i hΦc.measurable).aestronglyMeasurable
    have hQm : ∀ i : Fin N, MeasureTheory.AEStronglyMeasurable (Work.UBBInputs8.boxQInd V A i Φ)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      intro i
      have h1 : Measurable (fun x : Submission.BoseGases.X N =>
          A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
        ((measurable_const.indicator hAmeas).comp (measurable_pi_apply i)).mul hΦc.measurable
      have h2 : Work.UBBInputs8.boxQInd V A i Φ
          = fun x : Submission.BoseGases.X N =>
              A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd V A i Φ x := by
        funext x; rw [Work.UBBInputs8.boxQInd]
      rw [h2]
      exact (h1.sub (Work.BoseFixB1S.measurable_boxPInd V A hAmeas i hΦc.measurable)).aestronglyMeasurable
    have hPb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd V A i Φ x| ≤ CΦ :=
      fun i => Work.BoseFixB1S.abs_boxPInd_le hℓ (by rw [hVdef]; exact hvol) hAmeas hVreal hAc i hΦb
    have hQb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * CΦ := by
      intro i x hx
      have hP := hPb i x hx
      have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      have hprod : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ CΦ := by
        rw [abs_mul]
        calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * CΦ :=
              mul_le_mul hind (hΦb x hx) (abs_nonneg _) (by norm_num)
          _ = CΦ := one_mul CΦ
      have hsub : Work.UBBInputs8.boxQInd V A i Φ x
          = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd V A i Φ x := by
        rw [Work.UBBInputs8.boxQInd]
      rw [hsub]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd V A i Φ x|
          ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd V A i Φ x| := abs_sub _ _
        _ ≤ CΦ + CΦ := add_le_add hprod hP
        _ = 2 * CΦ := by ring
    -- the mass identity in the form required by the AM–GM
    have hmass : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * f (x i)) = ((4 * S / V) / 4) * M1 := by
      rw [hPmass]; ring
    have hAM := amgmSlotSumMeas (N := N) (ℓ := ℓ) hℓ
      (P := fun i => Work.UBBInputs8.boxPInd V A i Φ)
      (Q := fun i => Work.UBBInputs8.boxQInd V A i Φ)
      hPm hQm hPb hQb hfnn hfm hKfib0 hfb (A := 4 * S / V) (t := t) (W := M1) hApos hM1nn hmass
    exact amgmCombine (v := v) (M := M) (t := t) (V := V) (S := S) (QN := QN) (M1 := M1)
      (X0 := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x) * f (x i))
      (Qsum := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * f (x i))
      (by rw [hVdef]; exact hvol) hSnn hQNnn hM1nn hav hAM hQcnt

end Work.BoseFixB1
