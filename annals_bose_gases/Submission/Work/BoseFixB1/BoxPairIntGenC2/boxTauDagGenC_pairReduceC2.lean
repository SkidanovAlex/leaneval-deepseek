import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxD1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.boxTauDagGenC_pairReduceC2`

The C²-window box pair reduction of two `boxTauDagGenC` operators: for a measurable set
`A ⊆ acube ℓ` of volume `volA > 0`, a continuous `Φ`, and measurable *bounded* modes `g`, `g'`
vanishing off `A` with `∫_A g' = 0`,

    ∫_{abox (N+2) ℓ} Φ · τ†_g(τ†_{g'}Φ)
        = volA⁻¹ Σ_{i : Fin (N+2)} Σ_{j' : Fin (N+1)} ∫_{abox N ℓ} boxPairSlot · boxPairMean .

This is the genuine-box analogue of `Submission.Work.SmallBoxPairIdent.tau_pair_side`, with the
mode hypotheses relaxed from *continuous* (`Work.BoseFixB1.boxTauPairSide`,
`Work.BoseFixB1.boxPeelPairA`) to measurable + bounded on `A` — the form in which the C²-window
application (`Work.BoseFixB1.boxPairIntGenC2`) uses it.

The boundedness of the modes and the finiteness of `A` are exactly what is needed to make every
Bochner integral below a *genuine* one: without them the finite-sum/integral interchange fails
and the identity is false (`Work.BoseFixB1.boxTauPairPointwise_refuted`, where `A = univ` makes
`∫_A g'` a junk value).

## Structure

* `zIntegralC2Box` — the single-slot expansion of the inner creation operator (the diagonal
  `j = i` term is killed by `∫_A g' = 0`);
* `slotPairIntegrableC2Box` — the per-pair integrand is integrable on the box;
* `peelC2Box` — the per-slot-pair peel, factoring the box integral into
  `boxPairSlot · boxPairMean`;
* `pairReducePointwiseC2` — the pointwise double expansion, i.e. the pure algebra combining the
  two `(√volA)⁻¹` normalisations into `volA⁻¹` and reindexing the slot sums;
* the assembly: the pointwise expansion, the reindexing `Σ_{j ∈ erase i} = Σ_{j' : Fin (N+1)}`
  (`sum_erase_eq_succAbove`), `integral_finsetSum`, and the peel applied to each pair.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- The box indicator carried by `boxTauDagGenC` may be dropped for a mode supported in `A`. -/
lemma indicatorOneMulOfSupportC2 {A : Set ℝ³} {g : ℝ³ → ℂ}
    (hg : ∀ z, z ∉ A → g z = 0) (z : ℝ³) :
    A.indicator (fun _ => (1 : ℂ)) z * g z = g z := by
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz, one_mul]
  · rw [Set.indicator_of_notMem hz, zero_mul, hg z hz]

/-- `(√volA)⁻¹·(√volA)⁻¹ = volA⁻¹`, in the normalisation produced by the *definition*
`boxTauDagGenC` (the inverse is taken in `ℝ` first, then coerced). -/
lemma sqrtInvMulSqrtInvC2 {volA : ℝ} (h : 0 < volA) :
    (Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹ = ((volA⁻¹ : ℝ) : ℂ) := by
  have h1 : ((Real.sqrt volA)⁻¹ : ℝ) * ((Real.sqrt volA)⁻¹ : ℝ) = volA⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt h.le]
  rw [← Complex.ofReal_mul, h1]

/-- The same identity in the *ascribed* normalisation `(↑√volA)⁻¹·(↑√volA)⁻¹ = volA⁻¹`. -/
lemma sqrtInvMulSqrtInvAscC2 {volA : ℝ} (h : 0 < volA) :
    ((Real.sqrt volA)⁻¹ : ℂ) * ((Real.sqrt volA)⁻¹ : ℂ) = ((volA⁻¹ : ℝ) : ℂ) := by
  have h2 : (Real.sqrt volA : ℂ) * (Real.sqrt volA : ℂ) = ((volA : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h.le]
  calc ((Real.sqrt volA)⁻¹ : ℂ) * ((Real.sqrt volA)⁻¹ : ℂ)
      = (((Real.sqrt volA : ℂ) * (Real.sqrt volA : ℂ))⁻¹) := (mul_inv_rev _ _).symm
    _ = ((volA : ℂ))⁻¹ := by rw [h2]
    _ = ((volA⁻¹ : ℝ) : ℂ) := (Complex.ofReal_inv volA).symm

/-! ## Elementary facts about the box -/

/-- Updating one coordinate of a box configuration with a cube point keeps it in the box. -/
lemma updateMemAboxC2 {n : ℕ} {ℓ : ℝ} {x : X n} {k : Fin n} {v : ℝ³}
    (hx : x ∈ abox n ℓ) (hv : v ∈ acube ℓ) : Function.update x k v ∈ abox n ℓ := by
  rw [mem_abox_iff] at hx ⊢
  intro m
  by_cases h : m = k
  · subst h; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne h]; exact hx m

/-- Updating two coordinates of a box configuration with cube points keeps it in the box. -/
lemma updateUpdateMemAboxC2 {n : ℕ} {ℓ : ℝ} {x : X n} {a i : Fin n} {w v : ℝ³}
    (hx : x ∈ abox n ℓ) (hv : v ∈ acube ℓ) (hw : w ∈ acube ℓ) :
    Function.update (Function.update x a w) i v ∈ abox n ℓ :=
  updateMemAboxC2 (updateMemAboxC2 hx hw) hv

/-- A continuous `Φ` is bounded by a nonnegative constant on the box. -/
lemma phiBoundAboxC2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ abox n ℓ, ‖(Φ x : ℂ)‖ ≤ M := by
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  refine le_trans ?_ (le_max_left C 0)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hC x hx

/-- A subset of the cube has finite measure. -/
lemma volumeLtTopOfSubsetAcubeC2 {ℓ : ℝ} {A : Set ℝ³} (hℓ : 0 ≤ ℓ) (hAc : A ⊆ acube ℓ) :
    (volume : Measure ℝ³) A < ∞ :=
  lt_of_le_of_lt (measure_mono hAc) (acube_lt_top ℓ hℓ)

/-! ## The per-pair integrand is integrable on the box -/

theorem slotPairIntegrableC2Box {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (g g' : EuclideanSpace ℝ (Fin 3) → ℂ) (hgm : Measurable g) (hg'm : Measurable g')
    {C C' : ℝ} (hgC : ∀ z, ‖g z‖ ≤ C) (hg'C : ∀ z, ‖g' z‖ ≤ C')
    (hgs : ∀ z, z ∉ A → g z = 0) (hg's : ∀ z, z ∉ A → g' z = 0)
    (i j : Fin (N + 2)) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (N + 2) => (Φ x : ℂ) * g (x i) * g' (x j)
        * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x j z) i y) : ℂ)))
      (Submission.BoseGases.abox (N + 2) ℓ) MeasureTheory.volume := by
  classical
  obtain ⟨M, hM0, hM⟩ := phiBoundAboxC2 (n := N + 2) hℓ hΦc
  have hAfin : (volume : Measure ℝ³) A < ∞ := volumeLtTopOfSubsetAcubeC2 hℓ.le hAc
  have hCnn : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hgC 0)
  have hC'nn : 0 ≤ C' := le_trans (norm_nonneg (g' 0)) (hg'C 0)
  -- the inner double integral is bounded on the box
  have hinner : ∀ x ∈ abox (N + 2) ℓ,
      ‖∫ y in A, ∫ z in A, (Φ (Function.update (Function.update x j z) i y) : ℂ)‖
        ≤ (M * (volume A).toReal) * (volume A).toReal := by
    intro x hx
    have h1 : ∀ y ∈ A, ‖∫ z in A, (Φ (Function.update (Function.update x j z) i y) : ℂ)‖
        ≤ M * (volume A).toReal := by
      intro y hy
      refine norm_setIntegral_le_of_norm_le_const hAfin (fun z hz => ?_)
      have hmem : Function.update (Function.update x j z) i y ∈ abox (N + 2) ℓ :=
        updateUpdateMemAboxC2 (a := j) (i := i) (w := z) (v := y) hx (hAc hy) (hAc hz)
      simpa only [Complex.norm_real] using hM _ hmem
    exact norm_setIntegral_le_of_norm_le_const hAfin h1
  -- joint measurability of the inner double integral
  have hinner_meas : AEStronglyMeasurable (fun x : X (N + 2) =>
      ∫ y in A, ∫ z in A, (Φ (Function.update (Function.update x j z) i y) : ℂ))
      ((volume : Measure (X (N + 2))).restrict (abox (N + 2) ℓ)) := by
    have hcont : Continuous (fun q : (X (N + 2) × ℝ³) × ℝ³ =>
        (Φ (Function.update (Function.update q.1.1 j q.2) i q.1.2) : ℂ)) := by
      have h1 : Continuous (fun q : (X (N + 2) × ℝ³) × ℝ³ =>
          Function.update q.1.1 j q.2) :=
        (continuous_update_prod j).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
      have h2 : Continuous (fun q : (X (N + 2) × ℝ³) × ℝ³ =>
          Function.update (Function.update q.1.1 j q.2) i q.1.2) :=
        (continuous_update_prod i).comp (h1.prodMk (continuous_snd.comp continuous_fst))
      exact Complex.continuous_ofReal.comp (hΦc.comp h2)
    have h1 := AEStronglyMeasurable.integral_prod_right'
      (μ := ((volume : Measure (X (N + 2))).restrict (abox (N + 2) ℓ)).prod
        ((volume : Measure ℝ³).restrict A))
      (ν := (volume : Measure ℝ³).restrict A)
      (f := fun q : (X (N + 2) × ℝ³) × ℝ³ =>
        (Φ (Function.update (Function.update q.1.1 j q.2) i q.1.2) : ℂ))
      (hcont.aestronglyMeasurable (μ := (((volume : Measure (X (N + 2))).restrict
        (abox (N + 2) ℓ)).prod ((volume : Measure ℝ³).restrict A)).prod
        ((volume : Measure ℝ³).restrict A)))
    have h2 := AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure (X (N + 2))).restrict (abox (N + 2) ℓ))
      (ν := (volume : Measure ℝ³).restrict A)
      (f := fun q : X (N + 2) × ℝ³ =>
        ∫ z, (Φ (Function.update (Function.update q.1 j z) i q.2) : ℂ)
          ∂((volume : Measure ℝ³).restrict A))
      h1
    exact h2
  refine IntegrableOn.of_bound (abox_lt_top (N + 2) ℓ hℓ.le) ?_
    (C * C' * M * ((M * (volume A).toReal) * (volume A).toReal)) ?_
  · -- measurability of the full integrand
    have hfac : Measurable (fun x : X (N + 2) => (Φ x : ℂ) * g (x i) * g' (x j)) :=
      (((Complex.continuous_ofReal.comp hΦc).measurable).mul
        (hgm.comp (continuous_apply i).measurable)).mul
        (hg'm.comp (continuous_apply j).measurable)
    exact (hfac.aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul hinner_meas
  · -- the uniform bound on the box
    refine ae_restrict_of_forall_mem (abox_measurable (N + 2) ℓ) (fun x hx => ?_)
    have h1 : ‖(Φ x : ℂ)‖ ≤ M := hM x hx
    have h2 : ‖g (x i)‖ ≤ C := hgC _
    have h3 : ‖g' (x j)‖ ≤ C' := hg'C _
    have h4 := hinner x hx
    calc ‖(Φ x : ℂ) * g (x i) * g' (x j)
          * (∫ y in A, ∫ z in A, (Φ (Function.update (Function.update x j z) i y) : ℂ))‖
        = ‖(Φ x : ℂ)‖ * ‖g (x i)‖ * ‖g' (x j)‖
          * ‖∫ y in A, ∫ z in A, (Φ (Function.update (Function.update x j z) i y) : ℂ)‖ := by
          simp only [norm_mul]
      _ ≤ M * C * C' * ((M * (volume A).toReal) * (volume A).toReal) :=
          mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hM0) h3 (norm_nonneg _)
            (mul_nonneg hM0 hCnn)) h4 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hM0 hCnn) hC'nn)
      _ = C * C' * M * ((M * (volume A).toReal) * (volume A).toReal) := by ring

/-! ## The single-slot expansion of the inner creation operator -/

theorem zIntegralC2Box {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (g' : EuclideanSpace ℝ (Fin 3) → ℂ) (hg'm : Measurable g')
    {C' : ℝ} (hg'C : ∀ z, ‖g' z‖ ≤ C')
    (hg's : ∀ z, z ∉ A → g' z = 0) (hg'int : ∫ z in A, g' z = 0)
    (x : Submission.BoseGases.X (N + 2)) (hx : x ∈ Submission.BoseGases.abox (N + 2) ℓ)
    (i : Fin (N + 2)) :
    (∫ t in A, Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))
        (Function.update x i t))
      = ((Real.sqrt volA)⁻¹ : ℂ) * ∑ j ∈ Finset.univ.erase i,
          g' (x j) * ∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x j z) i y) : ℂ) := by
  classical
  obtain ⟨M, hM0, hM⟩ := phiBoundAboxC2 (n := N + 2) hℓ hΦc
  have hAfin : (volume : Measure ℝ³) A < ∞ := volumeLtTopOfSubsetAcubeC2 hℓ.le hAc
  have hC'nn : 0 ≤ C' := le_trans (norm_nonneg (g' 0)) (hg'C 0)
  -- integrability on `A` of each summand of the unfolded operator
  have hFk : ∀ k : Fin (N + 2), IntegrableOn (fun t : ℝ³ =>
      A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k) * g' ((Function.update x i t) k)
        * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ))) A volume := by
    intro k
    refine IntegrableOn.of_bound hAfin ?_ (C' * (M * (volume A).toReal)) ?_
    · -- a.e. strong measurability
      have hupd : Measurable (fun t : ℝ³ => (Function.update x i t) k) := by
        by_cases h : k = i
        · have hfun : (fun t : ℝ³ => (Function.update x i t) k) = fun t => t := by
            funext t; rw [← h, Function.update_self]
          rw [hfun]; exact measurable_id
        · have hfun : (fun t : ℝ³ => (Function.update x i t) k) = fun _ => x k := by
            funext t; rw [Function.update_of_ne h]
          rw [hfun]; exact measurable_const
      have hmeas1 : Measurable (fun t : ℝ³ =>
          A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
            * g' ((Function.update x i t) k)) :=
        ((measurable_const.indicator hA).comp hupd).mul (hg'm.comp hupd)
      have hcont : Continuous (fun q : ℝ³ × ℝ³ =>
          (Φ (Function.update (Function.update x i q.1) k q.2) : ℂ)) := by
        have ha : Continuous (fun q : ℝ³ × ℝ³ => Function.update x i q.1) :=
          (continuous_update_prod i).comp (continuous_const.prodMk continuous_fst)
        have hb : Continuous (fun q : ℝ³ × ℝ³ =>
            Function.update (Function.update x i q.1) k q.2) :=
          (continuous_update_prod k).comp (ha.prodMk continuous_snd)
        exact Complex.continuous_ofReal.comp (hΦc.comp hb)
      have hmeas2 : AEStronglyMeasurable (fun t : ℝ³ =>
          ∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ))
          ((volume : Measure ℝ³).restrict A) :=
        AEStronglyMeasurable.integral_prod_right'
          (μ := (volume : Measure ℝ³).restrict A) (ν := (volume : Measure ℝ³).restrict A)
          (f := fun q : ℝ³ × ℝ³ => (Φ (Function.update (Function.update x i q.1) k q.2) : ℂ))
          (hcont.aestronglyMeasurable (μ := ((volume : Measure ℝ³).restrict A).prod
            ((volume : Measure ℝ³).restrict A)))
      exact hmeas1.aestronglyMeasurable.mul hmeas2
    · -- the uniform bound
      refine ae_restrict_of_forall_mem hA (fun t ht => ?_)
      have h1 : ‖A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)‖ ≤ 1 := by
        by_cases hmem : (Function.update x i t) k ∈ A
        · rw [Set.indicator_of_mem hmem]; simp
        · rw [Set.indicator_of_notMem hmem]; simp
      have h2 : ‖g' ((Function.update x i t) k)‖ ≤ C' := hg'C _
      have h3 : ‖∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ)‖
          ≤ M * (volume A).toReal := by
        refine norm_setIntegral_le_of_norm_le_const hAfin (fun w hw => ?_)
        have hmem : Function.update (Function.update x i t) k w ∈ abox (N + 2) ℓ :=
          updateUpdateMemAboxC2 (a := i) (i := k) (w := t) (v := w) hx (hAc hw) (hAc ht)
        simpa only [Complex.norm_real] using hM _ hmem
      calc ‖A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
            * g' ((Function.update x i t) k)
            * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ))‖
          = ‖A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)‖
            * ‖g' ((Function.update x i t) k)‖
            * ‖∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ)‖ := by
            simp only [norm_mul]
        _ ≤ 1 * C' * (M * (volume A).toReal) :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _)
              (mul_nonneg (by norm_num) hC'nn)
        _ = C' * (M * (volume A).toReal) := by ring
  -- the diagonal (`k = i`) term vanishes
  have hdiag : (∫ t in A, A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) i)
      * g' ((Function.update x i t) i)
      * (∫ w in A, (Φ (Function.update (Function.update x i t) i w) : ℂ))) = 0 := by
    have h1 : (∫ t in A, A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) i)
        * g' ((Function.update x i t) i)
        * (∫ w in A, (Φ (Function.update (Function.update x i t) i w) : ℂ)))
        = ∫ t in A, g' t * (∫ w in A, (Φ (Function.update x i w) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hA] with t ht
      rw [Function.update_self, Set.indicator_of_mem ht, one_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with w
      rw [Function.update_idem]
    rw [h1, MeasureTheory.integral_mul_const, hg'int, zero_mul]
  -- assembly
  rw [show (∫ t in A, Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))
        (Function.update x i t))
      = ∫ t in A, (Real.sqrt volA)⁻¹ * ∑ k : Fin (N + 2),
          A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
            * g' ((Function.update x i t) k)
            * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ))
      from integral_congr_ae (Eventually.of_forall (fun t => rfl))]
  rw [MeasureTheory.integral_const_mul]
  rw [Complex.ofReal_inv]
  congr 1
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun k _ => hFk k)]
  rw [show (∑ k : Fin (N + 2), ∫ t in A,
        A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
          * g' ((Function.update x i t) k)
          * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ)))
      = (∑ k ∈ Finset.univ.erase i, ∫ t in A,
          A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
            * g' ((Function.update x i t) k)
            * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ)))
        + ∫ t in A, A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) i)
            * g' ((Function.update x i t) i)
            * (∫ w in A, (Φ (Function.update (Function.update x i t) i w) : ℂ))
      from (Finset.sum_erase_add (Finset.univ : Finset (Fin (N + 2)))
        (fun k => ∫ t in A, A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
          * g' ((Function.update x i t) k)
          * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ)))
        (Finset.mem_univ i)).symm]
  rw [hdiag, add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  rw [show (∫ t in A, A.indicator (fun _ => (1 : ℂ)) ((Function.update x i t) k)
        * g' ((Function.update x i t) k)
        * (∫ w in A, (Φ (Function.update (Function.update x i t) k w) : ℂ)))
      = ∫ t in A, g' (x k) * (∫ w in A,
          (Φ (Function.update (Function.update x k w) i t) : ℂ))
      from integral_congr_ae (Eventually.of_forall (fun t => by
        dsimp only
        rw [Function.update_of_ne hki]
        have hupd : (fun w : ℝ³ => (Φ (Function.update (Function.update x i t) k w) : ℂ))
            = fun w : ℝ³ => (Φ (Function.update (Function.update x k w) i t) : ℂ) := by
          funext w
          rw [Function.update_comm (Ne.symm hki) t w x]
        rw [hupd, indicatorOneMulOfSupportC2 hg's (x k)]))]
  rw [MeasureTheory.integral_const_mul]

/-- Bound for `boxPairMean` on the box. -/
lemma boxPairMeanNormLeC2 {N : ℕ} {ℓ : ℝ} {A : Set ℝ³} (hAc : A ⊆ acube ℓ)
    (hAfin : (volume : Measure ℝ³) A < ∞) {Φ : X (N + 2) → ℝ} {M : ℝ}
    (hM : ∀ x ∈ abox (N + 2) ℓ, ‖(Φ x : ℂ)‖ ≤ M)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) {r2 : X N} (hr2 : r2 ∈ abox N ℓ) :
    ‖Work.BoseFixB1.boxPairMean A Φ i j' r2‖ ≤ (M * (volume A).toReal) * (volume A).toReal := by
  rw [Work.BoseFixB1.boxPairMean]
  have h1 : ∀ y ∈ A, ‖∫ z in A, (Φ (ins2 i j' y z r2) : ℂ)‖ ≤ M * (volume A).toReal := by
    intro y hy
    refine norm_setIntegral_le_of_norm_le_const hAfin (fun z hz => ?_)
    simpa only [Complex.norm_real] using hM _ (ins2_mem_abox i j' (hAc hy) (hAc hz) hr2)
  exact norm_setIntegral_le_of_norm_le_const hAfin h1

theorem peelC2Box {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (g g' : EuclideanSpace ℝ (Fin 3) → ℂ) (hgm : Measurable g) (hg'm : Measurable g')
    {C C' : ℝ} (hgC : ∀ z, ‖g z‖ ≤ C) (hg'C : ∀ z, ‖g' z‖ ≤ C')
    (hgs : ∀ z, z ∉ A → g z = 0) (hg's : ∀ z, z ∉ A → g' z = 0)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    (∫ x in Submission.BoseGases.abox (N + 2) ℓ, (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ)))
      = ∫ r2 in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.boxPairSlot A Φ g g' i j' r2
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
  classical
  obtain ⟨M, hM0, hM⟩ := phiBoundAboxC2 (n := N + 2) hℓ hΦc
  have hAfin : (volume : Measure ℝ³) A < ∞ := volumeLtTopOfSubsetAcubeC2 hℓ.le hAc
  have hCnn : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hgC 0)
  have hC'nn : 0 ≤ C' := le_trans (norm_nonneg (g' 0)) (hg'C 0)
  -- the peeled integrand is integrable on the box
  have hFint : IntegrableOn (fun x : X (N + 2) => (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
      * (∫ y in A, ∫ z in A,
          (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ)))
      (abox (N + 2) ℓ) volume :=
    slotPairIntegrableC2Box hA hℓ hAc hvolA hvolpos hΦc g g' hgm hg'm hgC hg'C hgs hg's
      i (i.succAbove j')
  -- the value of the peeled integrand at the double insertion
  have hpt : ∀ y z : ℝ³, ∀ r2 : X N,
      (fun x : X (N + 2) => (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ y' in A, ∫ z' in A,
            (Φ (Function.update (Function.update x (i.succAbove j') z') i y') : ℂ)))
        (ins2 i j' y z r2)
      = (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
          * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
    intro y z r2
    dsimp only
    rw [ins2_apply_i, ins2_apply_succ]
    have hmean : (∫ y' in A, ∫ z' in A,
        (Φ (Function.update (Function.update (ins2 i j' y z r2) (i.succAbove j') z') i y') : ℂ))
        = Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
      rw [Work.BoseFixB1.boxPairMean]
      refine integral_congr_ae (Eventually.of_forall (fun y' => ?_))
      refine integral_congr_ae (Eventually.of_forall (fun z' => ?_))
      dsimp only
      rw [upd_upd_ins2]
    rw [hmean]
    ring
  -- the second peel, and the reduction of the cube integrals to `A`-integrals
  have hpeel : (∫ x in abox (N + 2) ℓ, (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ)))
      = ∫ r2 in abox N ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
    rw [abox_integral_peel2_gen (i := i) (j' := j')
      (F := fun x : X (N + 2) => (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ))) hFint]
    refine integral_congr_ae (Eventually.of_forall (fun r2 => ?_))
    refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    exact hpt y z r2
  have htoA : (∫ r2 in abox N ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
        (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
          * Work.BoseFixB1.boxPairMean A Φ i j' r2)
      = ∫ r2 in abox N ℓ, ∫ z in A, ∫ y in A,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
    refine integral_congr_ae (Eventually.of_forall (fun r2 => ?_))
    dsimp only
    have hy : (fun z : ℝ³ => ∫ y in acube ℓ, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
          * Work.BoseFixB1.boxPairMean A Φ i j' r2)
        = fun z : ℝ³ => ∫ y in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
          * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
      funext z
      exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (acube_measurable ℓ) hAc (fun y hy => by
          have hyA : y ∉ A := hy.2
          rw [hgs y hyA]; ring)
    rw [hy]
    exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (acube_measurable ℓ) hAc (fun z hz => by
        have hzero : (fun y : ℝ³ => (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2) = fun _ => (0 : ℂ) := by
          funext y
          rw [hg's z hz.2]; ring
        rw [hzero, MeasureTheory.integral_zero])
  -- Fubini: the two `A`-integrals may be interchanged
  have hswap : (∫ r2 in abox N ℓ, ∫ z in A, ∫ y in A,
        (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
          * Work.BoseFixB1.boxPairMean A Φ i j' r2)
      = ∫ r2 in abox N ℓ, ∫ y in A, ∫ z in A,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
    refine integral_congr_ae
      (ae_restrict_of_forall_mem (abox_measurable N ℓ) (fun r2 hr2 => ?_))
    haveI hfinA : IsFiniteMeasure ((volume : Measure ℝ³).restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
    haveI hfinAA : IsFiniteMeasure (((volume : Measure ℝ³).restrict A).prod
        ((volume : Measure ℝ³).restrict A)) := by
      constructor
      rw [Measure.prod_restrict, Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top hAfin hAfin
    refine MeasureTheory.integral_integral_swap (f := fun z y : ℝ³ =>
      (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
        * Work.BoseFixB1.boxPairMean A Φ i j' r2) ?_
    refine Integrable.of_bound ?_ (C * C' * M * ((M * (volume A).toReal) * (volume A).toReal)) ?_
    · -- measurability of the joint integrand
      have hcont : Continuous (fun q : ℝ³ × ℝ³ => ins2 i j' q.2 q.1 r2) :=
        (contDiff_ins2 i j').continuous.comp
          ((continuous_snd.prodMk continuous_fst).prodMk continuous_const)
      have hm : Measurable (fun q : ℝ³ × ℝ³ =>
          (Φ (ins2 i j' q.2 q.1 r2) : ℂ) * (g q.2 * g' q.1)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2) :=
        (((Complex.continuous_ofReal.comp (hΦc.comp hcont)).measurable).mul
          ((hgm.comp measurable_snd).mul (hg'm.comp measurable_fst))).mul measurable_const
      exact hm.aestronglyMeasurable
    · -- the uniform bound on `A × A`
      rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hA.prod hA) (fun q hq => ?_)
      have h1 : ‖g q.2‖ ≤ C := hgC _
      have h2 : ‖g' q.1‖ ≤ C' := hg'C _
      have h3 : ‖(Φ (ins2 i j' q.2 q.1 r2) : ℂ)‖ ≤ M :=
        hM _ (ins2_mem_abox i j' (hAc hq.2) (hAc hq.1) hr2)
      have h4 : ‖Work.BoseFixB1.boxPairMean A Φ i j' r2‖
          ≤ (M * (volume A).toReal) * (volume A).toReal :=
        boxPairMeanNormLeC2 hAc hAfin hM i j' hr2
      calc ‖(Φ (ins2 i j' q.2 q.1 r2) : ℂ) * (g q.2 * g' q.1)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2‖
          = ‖(Φ (ins2 i j' q.2 q.1 r2) : ℂ)‖ * ‖g q.2‖ * ‖g' q.1‖
            * ‖Work.BoseFixB1.boxPairMean A Φ i j' r2‖ := by
            simp only [norm_mul]; ring
        _ ≤ M * C * C' * ((M * (volume A).toReal) * (volume A).toReal) :=
            mul_le_mul (mul_le_mul (mul_le_mul h3 h1 (norm_nonneg _) hM0) h2 (norm_nonneg _)
              (mul_nonneg hM0 hCnn)) h4 (norm_nonneg _)
              (mul_nonneg (mul_nonneg hM0 hCnn) hC'nn)
        _ = C * C' * M * ((M * (volume A).toReal) * (volume A).toReal) := by ring
  -- identification with `boxPairSlot · boxPairMean`
  have hident : ∀ r2 : X N,
      (∫ y in A, ∫ z in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
          * Work.BoseFixB1.boxPairMean A Φ i j' r2)
        = Work.BoseFixB1.boxPairSlot A Φ g g' i j' r2
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
    intro r2
    have hH : (∫ y in A, ∫ z in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z))
        = ∫ y in A, ∫ z in A, g y * g' z * (Φ (ins2 i j' y z r2) : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
      refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
      ring
    calc (∫ y in A, ∫ z in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2)
        = (∫ y in A, ∫ z in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z))
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
          rw [show (∫ y in A, ∫ z in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
                * Work.BoseFixB1.boxPairMean A Φ i j' r2)
              = ∫ y in A, (∫ z in A, (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z))
                  * Work.BoseFixB1.boxPairMean A Φ i j' r2 from by
            refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
            dsimp only
            rw [MeasureTheory.integral_mul_const]]
          rw [MeasureTheory.integral_mul_const]
      _ = Work.BoseFixB1.boxPairSlot A Φ g g' i j' r2
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
          rw [Work.BoseFixB1.boxPairSlot, hH]
  calc (∫ x in abox (N + 2) ℓ, (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
        * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ)))
      = ∫ r2 in abox N ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := hpeel
    _ = ∫ r2 in abox N ℓ, ∫ z in A, ∫ y in A,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := htoA
    _ = ∫ r2 in abox N ℓ, ∫ y in A, ∫ z in A,
          (Φ (ins2 i j' y z r2) : ℂ) * (g y * g' z)
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := hswap
    _ = ∫ r2 in abox N ℓ,
          Work.BoseFixB1.boxPairSlot A Φ g g' i j' r2
            * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
        refine integral_congr_ae (Eventually.of_forall (fun r2 => hident r2))

/-! ## The pointwise double expansion -/

/-- **The pointwise double expansion.**  At a configuration `x` in the box, the double
creation operator pairing splits into the sum over ordered pairs of *distinct* slots, the
`j = i` diagonal being killed by `∫_A g' = 0`. -/
lemma pairReducePointwiseC2 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (g g' : EuclideanSpace ℝ (Fin 3) → ℂ) (hgm : Measurable g) (hg'm : Measurable g')
    {C C' : ℝ} (hgC : ∀ z, ‖g z‖ ≤ C) (hg'C : ∀ z, ‖g' z‖ ≤ C')
    (hgs : ∀ z, z ∉ A → g z = 0) (hg's : ∀ z, z ∉ A → g' z = 0)
    (hg'int : ∫ z in A, g' z = 0)
    (x : Submission.BoseGases.X (N + 2)) (hx : x ∈ Submission.BoseGases.abox (N + 2) ℓ) :
    (Φ x : ℂ) * Work.BoseFixB1.boxTauDagGenC volA A g
        (Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))) x
      = (volA⁻¹ : ℂ) * ∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
          (Φ x : ℂ) * g (x i) * g' (x j)
            * (∫ y in A, ∫ z in A,
                (Φ (Function.update (Function.update x j z) i y) : ℂ)) := by
  classical
  -- step 1: unfold the outer operator
  have h1 : Work.BoseFixB1.boxTauDagGenC volA A g
        (Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))) x
      = (Real.sqrt volA)⁻¹ * (∑ i : Fin (N + 2),
          A.indicator (fun _ => (1 : ℂ)) (x i) * g (x i)
            * (∫ t in A, Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))
                (Function.update x i t))) := rfl
  -- step 2: the single-slot expansion of the inner operator
  have h2 : ∀ i : Fin (N + 2),
      (∫ t in A, Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))
          (Function.update x i t))
        = ((Real.sqrt volA)⁻¹ : ℂ) * (∑ j ∈ Finset.univ.erase i,
            g' (x j) * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x j z) i y) : ℂ))) :=
    fun i => zIntegralC2Box hA hℓ hAc hvolA hvolpos hΦc g' hg'm hg'C hg's hg'int x hx i
  rw [h1]
  -- normalise the coefficient produced by the definition to the ascribed normalisation
  rw [Complex.ofReal_inv]
  have h3 : (∑ i : Fin (N + 2),
        A.indicator (fun _ => (1 : ℂ)) (x i) * g (x i)
          * (∫ t in A, Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))
              (Function.update x i t)))
      = ∑ i : Fin (N + 2),
          A.indicator (fun _ => (1 : ℂ)) (x i) * g (x i)
            * (((Real.sqrt volA)⁻¹ : ℂ) * (∑ j ∈ Finset.univ.erase i,
                g' (x j) * (∫ y in A, ∫ z in A,
                  (Φ (Function.update (Function.update x j z) i y) : ℂ)))) :=
    Finset.sum_congr rfl (fun i _ => by rw [h2 i])
  rw [h3]
  -- step 3: pure algebra
  have hL : (∑ i : Fin (N + 2),
        A.indicator (fun _ => (1 : ℂ)) (x i) * g (x i)
          * (((Real.sqrt volA)⁻¹ : ℂ) * (∑ j ∈ Finset.univ.erase i,
              g' (x j) * (∫ y in A, ∫ z in A,
                (Φ (Function.update (Function.update x j z) i y) : ℂ)))))
      = ((Real.sqrt volA)⁻¹ : ℂ) * (∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
            g (x i) * g' (x j) * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x j z) i y) : ℂ))) := by
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [indicatorOneMulOfSupportC2 hgs (x i)]
    rw [show g (x i) * (((Real.sqrt volA)⁻¹ : ℂ) * (∑ j ∈ Finset.univ.erase i,
          g' (x j) * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x j z) i y) : ℂ))))
        = ((Real.sqrt volA)⁻¹ : ℂ) * (g (x i) * (∑ j ∈ Finset.univ.erase i,
            g' (x j) * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x j z) i y) : ℂ)))) from by ring]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [hL]
  have hcoef : ((Real.sqrt volA)⁻¹ : ℂ) * ((Real.sqrt volA)⁻¹ : ℂ)
      = ((volA⁻¹ : ℝ) : ℂ) := sqrtInvMulSqrtInvAscC2 hvolpos
  have key : (Φ x : ℂ) * (∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
        g (x i) * g' (x j) * (∫ y in A, ∫ z in A,
          (Φ (Function.update (Function.update x j z) i y) : ℂ)))
      = ∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
          (Φ x : ℂ) * g (x i) * g' (x j) * (∫ y in A, ∫ z in A,
            (Φ (Function.update (Function.update x j z) i y) : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  rw [show (Φ x : ℂ) * (((Real.sqrt volA)⁻¹ : ℂ) * (((Real.sqrt volA)⁻¹ : ℂ)
        * (∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
            g (x i) * g' (x j) * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x j z) i y) : ℂ)))))
      = (((Real.sqrt volA)⁻¹ : ℂ) * ((Real.sqrt volA)⁻¹ : ℂ)) * ((Φ x : ℂ)
        * (∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
            g (x i) * g' (x j) * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x j z) i y) : ℂ)))) from by ring]
  rw [hcoef, Complex.ofReal_inv, key]

/-! ## The assembly -/

theorem boxTauDagGenC_pairReduceC2 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (g g' : EuclideanSpace ℝ (Fin 3) → ℂ) (hgm : Measurable g) (hg'm : Measurable g')
    {C C' : ℝ} (hgC : ∀ z, ‖g z‖ ≤ C) (hg'C : ∀ z, ‖g' z‖ ≤ C')
    (hgs : ∀ z, z ∉ A → g z = 0) (hg's : ∀ z, z ∉ A → g' z = 0)
    (hg'int : ∫ z in A, g' z = 0) :
    (∫ x in Submission.BoseGases.abox (N + 2) ℓ, (Φ x : ℂ)
        * Work.BoseFixB1.boxTauDagGenC volA A g
          (Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))) x)
      = (volA⁻¹ : ℂ) * ∑ i : Fin (N + 2), ∑ j' : Fin (N + 1),
          ∫ r2 in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1.boxPairSlot A Φ g g' i j' r2
              * Work.BoseFixB1.boxPairMean A Φ i j' r2 := by
  have hpt : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      (Φ x : ℂ) * Work.BoseFixB1.boxTauDagGenC volA A g
          (Work.BoseFixB1.boxTauDagGenC volA A g' (fun y => (Φ y : ℂ))) x
        = (volA⁻¹ : ℂ) * ∑ i : Fin (N + 2), ∑ j ∈ Finset.univ.erase i,
            (Φ x : ℂ) * g (x i) * g' (x j)
              * (∫ y in A, ∫ z in A,
                  (Φ (Function.update (Function.update x j z) i y) : ℂ)) :=
    fun x hx => pairReducePointwiseC2 hA hℓ hAc hvolA hvolpos hΦc g g' hgm hg'm hgC hg'C
      hgs hg's hg'int x hx
  rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable (N + 2) ℓ)
    hpt]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  simp only [Submission.BoseGases.sum_erase_eq_succAbove]
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ) (f := fun i (x : Submission.BoseGases.X (N + 2)) =>
        ∑ j' : Fin (N + 1), (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
          * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ)))
      (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ (fun j' _ =>
        (slotPairIntegrableC2Box hA hℓ hAc hvolA hvolpos hΦc g g' hgm hg'm hgC hg'C hgs hg's
          i (i.succAbove j')).integrable))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ) (f := fun j' (x : Submission.BoseGases.X (N + 2)) =>
        (Φ x : ℂ) * g (x i) * g' (x (i.succAbove j'))
          * (∫ y in A, ∫ z in A,
              (Φ (Function.update (Function.update x (i.succAbove j') z) i y) : ℂ)))
      (fun j' _ => (slotPairIntegrableC2Box hA hℓ hAc hvolA hvolpos hΦc g g' hgm hg'm hgC hg'C
        hgs hg's i (i.succAbove j')).integrable)]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  exact peelC2Box hA hℓ hAc hvolA hvolpos hΦc g g' hgm hg'm hgC hg'C hgs hg's i j'

end Work.BoseFixB1.BoxPairIntGenC2
