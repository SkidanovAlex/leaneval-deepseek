import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.mfPairRowManifestB1
import Submission.Work.BoseFixB1S.sum_pairSet_fst_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.mfManifestLowerV2B1`

The manifest lower bound of the flat branch of FS `thm:smallbox` (see
`Submission/Work/BoseFixB1S/FINDING_perBoxMeanFieldB1_SESSION10.md` §4, (MAN)).

With `ℓ = sideAt μ (a v)`, `A = boxA v μ u = dlBox ℓ d u`, `V = mfV v μ u = |A|`,
`W = boxW h μ u = wSmallPair M ℓ d u v`, `Pc = mfPc v μ n Φ u`, `Q = mfQ v μ n Φ u`,
`Mw = ∬_{A×A} W` and `Sq = Σ_{p∈pairSet n} ∫ (1_A(x_{p.1})(1_A(x_{p.2})Φ))²·W(x_{p.1},x_{p.2})`,

    (1/2)·Sq + 2·√(Kw·Mw·(n−1)·Q·Pc/(2V²)) ≥ (Mw/(2V²))·Pc .

The proof is the weighted Cauchy–Schwarz defect bound at the box projections, summed over the
ordered pairs, with the pair-projection identity `Σ_p∫(P_{p.1}P_{p.2}Φ)²W = (Mw/V²)·Pc`.

Everything is unconditional in the integrability of `W`: if `W` is not `L¹` on `A × A` then
`Mw = 0` and the claim degenerates to `Sq ≥ 0`, which holds pointwise.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary pieces -/

/-- `boxW` is non-negative when the potential is (`chiSmallB`, `chiSmall`, `convScale` are all
non-negative and the denominators are divisions of non-negative quantities). -/
theorem mfLV2_boxW_nonneg {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (μ : ℝ) (u : E3) :
    ∀ x y : E3, 0 ≤ boxW h μ u x y :=
  fun x y => wSmallPair_nonneg hv _ _ _ u x y

/-- The excited box count is non-negative. -/
theorem mfQ_nonneg' {v : E3 → ℝ} (μ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ)
    (u : E3) : 0 ≤ mfQ v μ n Φ u := by
  simp only [mfQ, Work.UBBInputs8.cnPlusBoxInd]
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

/-- The condensate pair count is non-negative. -/
theorem mfPc_nonneg' {v : E3 → ℝ} (μ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ)
    (u : E3) : 0 ≤ mfPc v μ n Φ u := by
  simp only [mfPc, Work.BoseFixB1S.boxPairCount]
  exact Finset.sum_nonneg fun p _ => integral_nonneg fun x => sq_nonneg _

/-- The second-coordinate analogue of `sum_pairSet_fst_eq`. -/
theorem sum_pairSet_snd_eq {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g p.2) = ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  have hinner : ∀ x : Fin N,
      (∑ y : Fin N, if x ≠ y then g y else 0) = (∑ y : Fin N, g y) - g x := by
    intro x
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter fun y : Fin N => x ≠ y) = Finset.univ.erase x := by
      ext y
      simp [Finset.mem_erase, ne_comm]
    rw [hf, Finset.sum_erase_eq_sub (Finset.mem_univ x)]
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hN : ((N : ℝ) - 1) * ∑ i : Fin N, g i
      = (N : ℝ) * (∑ i : Fin N, g i) - ∑ i : Fin N, g i := by ring
  rw [hN]

/-- `Σ_{p ∈ pairSet N}(g p.1 + g p.2) = 2(N−1)Σ_i g i`. -/
theorem sum_pairSet_add_eq {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, (g p.1 + g p.2))
      = 2 * ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  rw [Finset.sum_add_distrib, sum_pairSet_fst_eq, sum_pairSet_snd_eq]
  ring

/-! ## 2. The finite Cauchy–Schwarz and the summation of the per-pair rows -/

/-- Finite Cauchy–Schwarz for square roots. -/
theorem sumSqrtMulLeAux {ι : Type*} [DecidableEq ι] (s : Finset ι) (d b : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∑ i ∈ s, Real.sqrt (d i * b i) ≤ Real.sqrt ((∑ i ∈ s, d i) * (∑ i ∈ s, b i)) := by
  have h1 : ∑ i ∈ s, Real.sqrt (d i * b i)
      = ∑ i ∈ s, Real.sqrt (d i) * Real.sqrt (b i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Real.sqrt_mul (hd i hi)]
  rw [h1]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (d i)) (fun i => Real.sqrt (b i))
  have hD : (∑ i ∈ s, (Real.sqrt (d i)) ^ 2) = ∑ i ∈ s, d i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hd i hi)
  have hB : (∑ i ∈ s, (Real.sqrt (b i)) ^ 2) = ∑ i ∈ s, b i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hb i hi)
  rw [hD, hB] at h2
  have h4 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (Finset.sum_nonneg fun i hi =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h4

/-- Summation of the per-pair defect rows. -/
theorem sumPerPairLeAux {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b d : ι → ℝ)
    (hper : ∀ i ∈ s, b i - 2 * Real.sqrt (d i * b i) ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∑ i ∈ s, b i) - 2 * Real.sqrt ((∑ i ∈ s, d i) * (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, a i := by
  have hcs := sumSqrtMulLeAux s d b hd hb
  have h1 : ∑ i ∈ s, (b i - 2 * Real.sqrt (d i * b i)) ≤ ∑ i ∈ s, a i :=
    Finset.sum_le_sum hper
  have h2 : ∑ i ∈ s, (b i - 2 * Real.sqrt (d i * b i))
      = (∑ i ∈ s, b i) - 2 * ∑ i ∈ s, Real.sqrt (d i * b i) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [h2] at h1
  linarith

/-! ## 3. The closing arithmetic -/

/-- The closing arithmetic of the manifest lower bound: from the summed defect bound
`Sq ≥ Mw·Pc/V² − 2√(2·Kw·(n−1)·Q·Mw·Pc/V²)` conclude the manifest inequality. -/
theorem mfManifestArithAux {Mw Pc Q Kw Sq : ℝ} {n : ℕ} {V : ℝ}
    (hV : 0 < V) (hMw : 0 ≤ Mw) (hPc : 0 ≤ Pc)
    (hQn : 0 ≤ Kw * ((n : ℝ) - 1) * Q)
    (hSq : Mw * Pc / V ^ 2
        - 2 * Real.sqrt ((2 * Kw * ((n : ℝ) - 1) * Q) * (Mw * Pc / V ^ 2)) ≤ Sq) :
    (1 / 2) * Sq + 2 * Real.sqrt (Kw * Mw * ((n : ℝ) - 1) * Q * Pc / (2 * V ^ 2))
      ≥ (Mw / (2 * V ^ 2)) * Pc := by
  set b : ℝ := Kw * ((n : ℝ) - 1) * Q with hb
  set a : ℝ := Mw * Pc / V ^ 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; exact hQn
  have h2b : (2 : ℝ) * Kw * ((n : ℝ) - 1) * Q = 2 * b := by rw [hb]; ring
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hkey : Real.sqrt (2 * b * a) = 2 * Real.sqrt (b * a / 2) := by
    rw [show (2 : ℝ) * b * a = 4 * (b * a / 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
  have harg : Kw * Mw * ((n : ℝ) - 1) * Q * Pc / (2 * V ^ 2) = b * a / 2 := by
    rw [hb, ha]
    field_simp
  have hfinal : (Mw / (2 * V ^ 2)) * Pc = a / 2 := by
    rw [ha]
    field_simp
  rw [h2b] at hSq
  rw [hkey] at hSq
  rw [harg, hfinal]
  linarith

/-! ## 3b. The support and the integrability of the localised pair kernel -/

/-- `boxW` unfolded into its three factors. -/
theorem mfLV2_boxW_factor {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (u x y : E3) :
    Work.BoseFixB1S.boxW h μ u x y
      = Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
        * (Submission.BoseGases.wSmallScaled (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
              v (x - y)
            / Submission.BoseGases.convScale (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (x - y))
        * Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y := rfl

/-- The localised pair kernel vanishes outside the sliding box `B(u)` in each slot. -/
theorem mfLV2_boxW_support {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (u : E3)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    ∀ x y : E3, Work.BoseFixB1S.boxW h μ u x y ≠ 0 →
      x ∈ Work.BoseFixB1S.boxA v μ u ∧ y ∈ Work.BoseFixB1S.boxA v μ u := by
  intro x y hxy
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; decide
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3))
  constructor
  · refine Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd ?_
    intro h0
    exact hxy (by rw [mfLV2_boxW_factor, h0]; ring)
  · refine Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd ?_
    intro h0
    exact hxy (by rw [mfLV2_boxW_factor, h0]; ring)

/-- **Integrability of the localised pair kernel in a slot pair.**  If `W = boxW h μ u` is
`L¹` on `A × A` (`A = boxA v μ u`) then `x ↦ W (x i) (x j)` is `L¹` on `abox n ℓ` for every
distinct pair of slots.

The two `L¹`-statements differ by: the indicator form of `W` on the two-cube product
(`Q0C.integrable_indicator_pair`), the fact that `W` vanishes off `A × A`
(`mfLV2_boxW_support`), the lift to `ν₁ ⊗ ν₂` (`Measure.quasiMeasurePreserving_fst` plus
Tonelli), and the two-slot peel `eIns2` (measure-preserving, `Q0C.mp_eIns2`). -/
theorem mfLV2_boxW_boxIntegrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (u : E3)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hWint : MeasureTheory.Integrable
      (fun p : E3 × E3 => Work.BoseFixB1S.boxW h μ u p.1 p.2)
      (MeasureTheory.volume.restrict (Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u))) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseFixB1S.boxW h μ u (x i) (x j))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push_neg at hcon
    exact hij (Fin.ext (by omega))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  subst hj'
  have hAmeas : MeasurableSet (Work.BoseFixB1S.boxA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hAc : Work.BoseFixB1S.boxA v μ u
      ⊆ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  have hoff := mfLV2_boxW_support (v := v) h hμ hav u hℓ
  -- ### Step 1: integrability on the two-cube product measure
  have hν₁ : MeasureTheory.Integrable
      (fun t : E3 × E3 => Work.BoseFixB1S.boxW h μ u t.1 t.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) := by
    have h0 := Q0C.integrable_indicator_pair
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (A := Work.BoseFixB1S.boxA v μ u) hAmeas hAc hWint
    refine h0.congr ?_
    filter_upwards with q
    by_cases h1 : q.1 ∈ Work.BoseFixB1S.boxA v μ u
    · by_cases h2 : q.2 ∈ Work.BoseFixB1S.boxA v μ u
      · simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · have hz : Work.BoseFixB1S.boxW h μ u q.1 q.2 = 0 := by
          by_contra hc
          exact h2 (hoff q.1 q.2 hc).2
        simp [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, hz]
    · have hz : Work.BoseFixB1S.boxW h μ u q.1 q.2 = 0 := by
        by_contra hc
        exact h1 (hoff q.1 q.2 hc).1
      simp [Set.indicator_of_notMem h1, hz]
  -- ### Step 2: lift to the product with the remaining box
  haveI : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure
      (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (Submission.BoseGases.abox_lt_top m _ hℓ.le))
  have hbase : MeasureTheory.Integrable
      (fun q : (E3 × E3) × Submission.BoseGases.X m =>
        Work.BoseFixB1S.boxW h μ u q.1.1 q.1.2)
      ((((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
    hν₁.comp_fst _
  -- ### Step 3: peel
  have hcomp : MeasureTheory.Integrable
      ((fun x : Submission.BoseGases.X (m + 2) =>
          Work.BoseFixB1S.boxW h μ u (x i) (x (i.succAbove j')))
        ∘ ⇑(Q0C.eIns2 i j'))
      ((((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
    hbase.congr (by
      filter_upwards with q
      simp only [Function.comp_apply, Q0C.eIns2_apply_i, Q0C.eIns2_apply_succ])
  exact ((Q0C.mp_eIns2 (p := m) hℓ i j').integrable_comp_emb
    (Q0C.eIns2 i j').measurableEmbedding).mp hcomp

/-! ## 3c. The weighted Cauchy–Schwarz on a measure -/

/-- The quadratic discriminant lemma: if `A ≥ 0` and the quadratic `λ ↦ λ²A − 2λC + B` is
non-negative for all real `λ`, then `C² ≤ A·B`. -/
theorem mfLV2_quadDisc {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ s : ℝ, 0 ≤ s ^ 2 * A - 2 * s * C + B) : C ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hB0 : 0 ≤ B := by
      have hh := h 0
      simpa using hh
    have h1 : C = 0 := by
      by_contra hC
      have h2 := h ((B + 1) / (2 * C))
      rw [hA0] at h2
      have h4 : -2 * ((B + 1) / (2 * C)) * C + B = -1 := by
        field_simp
        ring
      nlinarith [h2, h4]
    rw [h1]
    nlinarith [hA, hB0]
  · have h2 := h (C / A)
    have h3 : (C / A) ^ 2 * A - 2 * (C / A) * C + B = B - C ^ 2 / A := by
      field_simp
      ring
    rw [h3] at h2
    have h4 : C ^ 2 / A ≤ B := by linarith
    calc C ^ 2 = A * (C ^ 2 / A) := by field_simp
      _ ≤ A * B := mul_le_mul_of_nonneg_left h4 hA

/-- **The weighted Cauchy–Schwarz inequality** on a measure, for a non-negative weight `w`. -/
theorem mfLV2_weightedCS {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {a b w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ha : MeasureTheory.Integrable (fun x => a x ^ 2 * w x) μ)
    (hb : MeasureTheory.Integrable (fun x => b x ^ 2 * w x) μ)
    (hab : MeasureTheory.Integrable (fun x => a x * b x * w x) μ) :
    (∫ x, a x * b x * w x ∂μ) ^ 2
      ≤ (∫ x, a x ^ 2 * w x ∂μ) * (∫ x, b x ^ 2 * w x ∂μ) := by
  refine mfLV2_quadDisc (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)) ?_
  intro s
  have hexpp : (fun x => (s * a x - b x) ^ 2 * w x)
      = fun x => s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x) + (b x ^ 2 * w x) := by
    funext x; ring
  have hsplit : (fun x => (s * a x - b x) ^ 2 * w x)
      = (fun x => s ^ 2 * (a x ^ 2 * w x)) - (fun x => 2 * s * (a x * b x * w x))
        + (fun x => b x ^ 2 * w x) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hInt : MeasureTheory.Integrable (fun x => (s * a x - b x) ^ 2 * w x) μ := by
    rw [hsplit]
    exact ((ha.const_mul _).sub (hab.const_mul _)).add hb
  have h0 : 0 ≤ ∫ x, (s * a x - b x) ^ 2 * w x ∂μ :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw x)
  have hexp : (∫ x, (s * a x - b x) ^ 2 * w x ∂μ)
      = s ^ 2 * (∫ x, a x ^ 2 * w x ∂μ) - 2 * s * (∫ x, a x * b x * w x ∂μ)
        + (∫ x, b x ^ 2 * w x ∂μ) := by
    have h1 : (∫ x, (s * a x - b x) ^ 2 * w x ∂μ)
        = ∫ x, (s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x)) + (b x ^ 2 * w x) ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      ring
    have h2 : (∫ x, (s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x))
          + (b x ^ 2 * w x) ∂μ)
        = (∫ x, s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x) ∂μ)
          + (∫ x, b x ^ 2 * w x ∂μ) :=
      MeasureTheory.integral_add ((ha.const_mul _).sub (hab.const_mul _)) hb
    have h3 : (∫ x, s ^ 2 * (a x ^ 2 * w x) - 2 * s * (a x * b x * w x) ∂μ)
        = (∫ x, s ^ 2 * (a x ^ 2 * w x) ∂μ) - (∫ x, 2 * s * (a x * b x * w x) ∂μ) :=
      MeasureTheory.integral_sub (ha.const_mul _) (hab.const_mul _)
    have h4 : (∫ x, s ^ 2 * (a x ^ 2 * w x) ∂μ) = s ^ 2 * (∫ x, a x ^ 2 * w x ∂μ) :=
      MeasureTheory.integral_const_mul (s ^ 2) (f := fun x => a x ^ 2 * w x)
    have h5 : (∫ x, 2 * s * (a x * b x * w x) ∂μ)
        = (2 * s) * (∫ x, a x * b x * w x ∂μ) :=
      MeasureTheory.integral_const_mul (2 * s) (f := fun x => a x * b x * w x)
    rw [h1, h2, h3, h4, h5]
  linarith [h0, hexp]

/-! ## 3d. The three slot functions of one ordered pair, and the per-pair row -/

/-- The truncated two-slot state of an ordered pair. -/
abbrev mfLV2sig (v : E3 → ℝ) (μ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (u : E3) (p : Fin n × Fin n) : Submission.BoseGases.X n → ℝ :=
  fun x => (Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
    * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)

/-- The two-slot condensate projection of an ordered pair. -/
abbrev mfLV2gg (v : E3 → ℝ) (μ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (u : E3) (p : Fin n × Fin n) : Submission.BoseGases.X n → ℝ :=
  fun x => Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
    (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x

/-- The localised pair kernel along an ordered pair. -/
abbrev mfLV2ww {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3)
    {n : ℕ} (p : Fin n × Fin n) : Submission.BoseGases.X n → ℝ :=
  fun x => Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2)

/-- **The per-pair row.**  With the weighted Cauchy–Schwarz on the vector pair
`(σ − g, g)` in the weight `w`, and the two defect inputs `0 ≤ ∫(σ−g)²w` and
`∫(σ−g)² ≤ D`, `w ≤ Kw`,

    ∫g²w − 2√(Kw·D·∫g²w) ≤ ∫σ²w . -/
theorem mfLV2_pairRow {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {σ g w : α → ℝ} {Kw D : ℝ}
    (hσ2 : MeasureTheory.Integrable (fun x => σ x ^ 2 * w x) μ)
    (hg2 : MeasureTheory.Integrable (fun x => g x ^ 2 * w x) μ)
    (hσg : MeasureTheory.Integrable (fun x => σ x * g x * w x) μ)
    (heg : MeasureTheory.Integrable (fun x => (σ x - g x) * g x * w x) μ)
    (he2 : MeasureTheory.Integrable (fun x => (σ x - g x) ^ 2 * w x) μ)
    (he2u : MeasureTheory.Integrable (fun x => (σ x - g x) ^ 2) μ)
    (hwnn : ∀ x, 0 ≤ w x) (hwle : ∀ x, w x ≤ Kw) (hKw : 0 ≤ Kw)
    (hD : ∫ x, (σ x - g x) ^ 2 ∂μ ≤ D) :
    (∫ x, g x ^ 2 * w x ∂μ)
        - 2 * Real.sqrt (Kw * D * (∫ x, g x ^ 2 * w x ∂μ))
      ≤ ∫ x, σ x ^ 2 * w x ∂μ := by
  set A := ∫ x, σ x ^ 2 * w x ∂μ with hA
  set B := ∫ x, g x ^ 2 * w x ∂μ with hB
  set C := ∫ x, σ x * g x * w x ∂μ with hC
  set E := ∫ x, (σ x - g x) ^ 2 * w x ∂μ with hE
  set E0 := ∫ x, (σ x - g x) ^ 2 ∂μ with hE0
  have hBnn : 0 ≤ B := by
    rw [hB]; exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hwnn x)
  have hEnn : 0 ≤ E := by
    rw [hE]; exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hwnn x)
  have hEE0 : E ≤ Kw * E0 := by
    have hK : MeasureTheory.Integrable (fun x => Kw * ((σ x - g x) ^ 2)) μ :=
      he2u.const_mul Kw
    have h1 : E ≤ ∫ x, Kw * ((σ x - g x) ^ 2) ∂μ := by
      rw [hE]
      refine MeasureTheory.integral_mono_ae he2 hK ?_
      filter_upwards with x
      calc (σ x - g x) ^ 2 * w x ≤ (σ x - g x) ^ 2 * Kw :=
            mul_le_mul_of_nonneg_left (hwle x) (sq_nonneg _)
        _ = Kw * ((σ x - g x) ^ 2) := by ring
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1
  have hEKD : E ≤ Kw * D := by
    rw [hE0] at hD
    exact le_trans hEE0 (mul_le_mul_of_nonneg_left hD hKw)
  have hcs : C - B = ∫ x, (σ x - g x) * g x * w x ∂μ := by
    rw [hC, hB, ← MeasureTheory.integral_sub hσg hg2]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    ring
  have hcs2 : (∫ x, (σ x - g x) * g x * w x ∂μ) ^ 2 ≤ E * B := by
    rw [hE, hB]
    exact mfLV2_weightedCS hwnn he2 hg2 heg
  have hsqr : (C - B) ^ 2 ≤ E * B := by rw [hcs]; exact hcs2
  have hAB : A - B = E + 2 * (C - B) := by
    have h1 : A - B = ∫ x, (σ x ^ 2 * w x - g x ^ 2 * w x) ∂μ := by
      rw [hA, hB, MeasureTheory.integral_sub hσ2 hg2]
    rw [h1, hcs]
    have h2 : (∫ x, (σ x ^ 2 * w x - g x ^ 2 * w x) ∂μ)
        = ∫ x, ((σ x - g x) ^ 2 * w x + 2 * ((σ x - g x) * g x * w x)) ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      ring
    rw [h2, MeasureTheory.integral_add he2 (heg.const_mul _),
      MeasureTheory.integral_const_mul, hE]
  have hkey : -(Real.sqrt (E * B)) ≤ C - B := by
    have h1 : |C - B| ≤ Real.sqrt (E * B) := by
      rw [← Real.sqrt_sq (abs_nonneg (C - B)), sq_abs]
      exact Real.sqrt_le_sqrt hsqr
    linarith [neg_le_abs (C - B), h1]
  have hEB : Real.sqrt (E * B) ≤ Real.sqrt (Kw * D * B) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hEKD hBnn)
  have hmain : B - 2 * Real.sqrt (Kw * D * B) ≤ A := by
    linarith [hAB, hkey, hEB]
  simpa only [hA, hB] using hmain

/-- Integrability of `F·w` from an a.e. bound on `F` and integrability of `Cv·|w|`. -/
theorem mfLV2_mono1 {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F w : α → ℝ} {Cv : ℝ} (hC : 0 ≤ Cv)
    (hm : AEStronglyMeasurable (fun x => F x * w x) μ)
    (hb : ∀ᵐ x ∂μ, |F x| ≤ Cv) (hW : MeasureTheory.Integrable (fun x => Cv * |w x|) μ) :
    MeasureTheory.Integrable (fun x => F x * w x) μ := by
  refine MeasureTheory.Integrable.mono' hW hm ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- Integrability of `F·G·w` from a.e. bounds on `F` and `G`. -/
theorem mfLV2_mono2 {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F G w : α → ℝ} {CvA CvB : ℝ} (hA : 0 ≤ CvA) (hB : 0 ≤ CvB)
    (hm : AEStronglyMeasurable (fun x => F x * G x * w x) μ)
    (h1 : ∀ᵐ x ∂μ, |F x| ≤ CvA) (h2 : ∀ᵐ x ∂μ, |G x| ≤ CvB)
    (hW : MeasureTheory.Integrable (fun x => CvA * CvB * |w x|) μ) :
    MeasureTheory.Integrable (fun x => F x * G x * w x) μ := by
  refine MeasureTheory.Integrable.mono' hW hm ?_
  filter_upwards [h1, h2] with x hx1 hx2
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hx1 hx2 (abs_nonneg _) hA) (abs_nonneg _)

/-- Integrability of `F` from an a.e. uniform bound on a finite-measure space. -/
theorem mfLV2_monoNoW {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [IsFiniteMeasure μ] {F : α → ℝ} {Cv : ℝ} (hm : AEStronglyMeasurable F μ)
    (hb : ∀ᵐ x ∂μ, |F x| ≤ Cv) : MeasureTheory.Integrable F μ := by
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const Cv) hm ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs]
  exact hx

/-! ## 4. The main theorem -/

theorem mfManifestLowerV2B1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {μ Kw : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hV : 0 < Work.BoseFixB1S.mfV v μ u) (hΦc : Continuous Φ)
    (hsupp : Work.BoseFixB1S.mfSupp v μ n Φ u)
    (hKw : ∀ x y : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1S.boxW h μ u x y ≤ Kw) :
    (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
              * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      + 2 * Real.sqrt (Kw * (∫ p in Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u,
              Work.BoseFixB1S.boxW h μ u p.1 p.2) * ((n : ℝ) - 1)
            * Work.BoseFixB1S.mfQ v μ n Φ u * Work.BoseFixB1S.mfPc v μ n Φ u
            / (2 * (Work.BoseFixB1S.mfV v μ u) ^ 2))
      ≥ ((∫ p in Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u,
              Work.BoseFixB1S.boxW h μ u p.1 p.2) / (2 * (Work.BoseFixB1S.mfV v μ u) ^ 2))
          * Work.BoseFixB1S.mfPc v μ n Φ u := by
  classical
  by_cases hWint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1S.boxW h μ u p.1 p.2)
      (MeasureTheory.volume.restrict
        (Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u))
  · -- ### Case B: `W` is `L¹` on `A × A`, the Cauchy–Schwarz defect argument applies
    set Mwb : ℝ := ∫ p in Work.BoseFixB1S.boxA v μ u ×ˢ Work.BoseFixB1S.boxA v μ u,
      Work.BoseFixB1S.boxW h μ u p.1 p.2 with hMwb
    set Qb : ℝ := Work.BoseFixB1S.mfQ v μ n Φ u with hQb
    set Pcb : ℝ := Work.BoseFixB1S.mfPc v μ n Φ u with hPcb
    set bnd : Fin n × Fin n → ℝ := fun p =>
      ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
          (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) with hbnd
    set hand : Fin n × Fin n → ℝ := fun p =>
      ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
            * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) with hhand
    set hdnd : Fin n × Fin n → ℝ := fun p =>
      Kw * ((∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1 Φ x) ^ 2)
            + (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ x) ^ 2))
      with hhdnd
    have hWnn : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixB1S.boxW h μ u x y :=
      mfLV2_boxW_nonneg h hv μ u
    have hMwnn : 0 ≤ Mwb := by
      rw [hMwb]
      exact integral_nonneg fun p => hWnn p.1 p.2
    have hQnn : 0 ≤ Qb := by rw [hQb]; exact mfQ_nonneg' μ n Φ u
    have hPcnn : 0 ≤ Pcb := by rw [hPcb]; exact mfPc_nonneg' μ n Φ u
    have hKwnn : 0 ≤ Kw := le_trans (hWnn 0 0) (hKw 0 0)
    have hQn : 0 ≤ Kw * ((n : ℝ) - 1) * Qb := by
      cases n with
      | zero =>
        have hQ0 : Qb = 0 := by
          rw [hQb, Work.BoseFixB1S.mfQ, Work.UBBInputs8.cnPlusBoxInd]
          exact Fin.sum_univ_zero _
        rw [hQ0]; norm_num
      | succ m =>
        have hm0 : (0 : ℝ) ≤ ((m : ℝ) + 1 - 1) := by simp
        have h := mul_nonneg (mul_nonneg hKwnn hm0) hQnn
        simpa [Nat.cast_add, Nat.cast_one] using h
    -- The per-pair weighted Cauchy–Schwarz defect bound.
    have hpair : ∀ p ∈ Submission.BoseGases.pairSet n,
        bnd p - 2 * Real.sqrt (hdnd p * bnd p) ≤ hand p := by
      intro p hp
      have hKwnn' : 0 ≤ Kw := le_trans (mfLV2_boxW_nonneg h hv μ u 0 0) (hKw 0 0)
      have hbnn' : 0 ≤ bnd p := by
        simp only [hbnd]
        exact integral_nonneg fun x =>
          mul_nonneg (sq_nonneg _) (mfLV2_boxW_nonneg h hv μ u (x p.1) (x p.2))
      have hdnn' : 0 ≤ hdnd p := by
        simp only [hhdnd]
        exact mul_nonneg hKwnn'
          (add_nonneg (integral_nonneg fun x => sq_nonneg _)
            (integral_nonneg fun x => sq_nonneg _))
      have h1 := mfPairRowManifestB1 (v := v) (R := R) (Kw := Kw) (μ := μ) (n := n)
        h hv hR hv_supp hav hμ Φ u hℓ hV hΦc hsupp hKw hWint hp
      rw [Real.sqrt_mul hdnn' (bnd p)]
      simp only [hhand, hbnd, hhdnd] at h1 ⊢
      linarith [h1]
    have hbnn : ∀ p ∈ Submission.BoseGases.pairSet n, 0 ≤ bnd p := by
      intro p _
      simp only [hbnd]
      exact integral_nonneg fun x =>
        mul_nonneg (sq_nonneg _) (mfLV2_boxW_nonneg h hv μ u (x p.1) (x p.2))
    have hdnn : ∀ p ∈ Submission.BoseGases.pairSet n, 0 ≤ hdnd p := by
      intro p _
      simp only [hhdnd]
      refine mul_nonneg hKwnn (add_nonneg ?_ ?_) <;>
        exact integral_nonneg fun x => sq_nonneg _
    have hsum := sumPerPairLeAux (Submission.BoseGases.pairSet n) hand bnd hdnd hpair hbnn hdnn
    -- The pair-projection identity `Σ_p∫(P_{p.1}P_{p.2}Φ)²W = (Mw/V²)·Pc`.
    have hPcmass : (∑ p ∈ Submission.BoseGases.pairSet n, bnd p)
        = Mwb * Pcb / (Work.BoseFixB1S.mfV v μ u) ^ 2 := by
      have hAmeas : MeasurableSet (Work.BoseFixB1S.boxA v μ u) :=
        Work.SmallBoxSliding.measurableSet_dlBox _ _ _
      have hvolA : Work.BoseFixB1S.mfV v μ u
          = (MeasureTheory.volume : MeasureTheory.Measure E3).real (Work.BoseFixB1S.boxA v μ u) :=
        Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _
      have hAc : Work.BoseFixB1S.boxA v μ u
          ⊆ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
        Work.SmallBoxSliding.dlBox_subset_acube _ _ _
      have hper : ∀ p ∈ Submission.BoseGases.pairSet n,
          bnd p = (Mwb / (Work.BoseFixB1S.mfV v μ u) ^ 2) *
            (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
                (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2) := by
        intro p hp
        have hij : p.1 ≠ p.2 := by
          simpa [Submission.BoseGases.pairSet] using hp
        have h := Q0C.pair_value (N := n)
          (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (volA := Work.BoseFixB1S.mfV v μ u)
          hℓ hV hAmeas hvolA hAc (i := p.1) (j := p.2) hij hWint hΦc
        simp only [hbnd]
        rw [h]
        congr 1
      have hPce : (∑ p ∈ Submission.BoseGases.pairSet n,
            (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
                (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2))
          = Pcb := by
        rw [hPcb]
        rfl
      rw [Finset.sum_congr rfl hper, ← Finset.mul_sum, hPce]
      ring
    have hDsum : (∑ p ∈ Submission.BoseGases.pairSet n, hdnd p)
        = 2 * Kw * ((n : ℝ) - 1) * Qb := by
      have hstep : (∑ p ∈ Submission.BoseGases.pairSet n, hdnd p)
          = Kw * ∑ p ∈ Submission.BoseGases.pairSet n,
              ((∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1 Φ x) ^ 2)
                + (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ x) ^ 2)) := by
        rw [hhdnd, Finset.mul_sum]
      have hstep2 : (∑ p ∈ Submission.BoseGases.pairSet n,
              ((∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1 Φ x) ^ 2)
                + (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ x) ^ 2)))
          = 2 * ((n : ℝ) - 1) * Qb := by
        have hg := sum_pairSet_add_eq (N := n)
          (fun i : Fin n =>
            ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) i Φ x) ^ 2)
        rw [hg]
        rfl
      rw [hstep, hstep2]
      ring
    have hSq : Mwb * Pcb / (Work.BoseFixB1S.mfV v μ u) ^ 2
        - 2 * Real.sqrt ((2 * Kw * ((n : ℝ) - 1) * Qb)
            * (Mwb * Pcb / (Work.BoseFixB1S.mfV v μ u) ^ 2))
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n, hand p := by
      rw [← hPcmass, ← hDsum]
      exact hsum
    exact mfManifestArithAux hV hMwnn hPcnn hQn hSq
  · -- ### Case A: `W` is not `L¹(A × A)`, so `Mw = 0` and the claim degenerates
    have hSqnn : 0 ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
              * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) :=
      Finset.sum_nonneg fun p _ => integral_nonneg fun x =>
        mul_nonneg (sq_nonneg _) (mfLV2_boxW_nonneg h hv μ u (x p.1) (x p.2))
    rw [MeasureTheory.integral_undef hWint]
    simp only [mul_zero, zero_mul, zero_div, Real.sqrt_zero, add_zero]
    linarith

end

end Work.BoseFixB1S
