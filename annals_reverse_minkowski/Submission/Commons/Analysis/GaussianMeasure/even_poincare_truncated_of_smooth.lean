import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Set Real Filter
open scoped Real Topology

noncomputable section

/-- The whole-space "even Poincaré for a `C²` even `2π`-strongly convex potential" statement,
packaged so that it can be threaded through the truncation argument. -/
abbrev EvenPoincareSmooth : Prop :=
  ∀ (m : ℕ) (g h : EuclideanSpace ℝ (Fin m) → ℝ),
    ContDiff ℝ 2 g →
    (∀ x v : EuclideanSpace ℝ (Fin m), 2 * Real.pi * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ g) x v v) →
    ConvexOn ℝ Set.univ (fun x => g x - Real.pi * ‖x‖ ^ 2) →
    (∀ x : EuclideanSpace ℝ (Fin m), g (-x) = g x) →
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin m),
      |fderiv ℝ g x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ g) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) →
    ContDiff ℝ 1 h →
    (∀ x : EuclideanSpace ℝ (Fin m), h (-x) = h x) →
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin m),
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) →
    (∫ x, h x ^ 2 * Real.exp (-(g x)))
        - (∫ x, h x * Real.exp (-(g x))) ^ 2 / (∫ x, Real.exp (-(g x)))
      ≤ (1 / (4 * Real.pi)) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(g x))

/-! ### Evenness of the truncated Gaussian data

For symmetric `A` the penalised potential `penF n A ε` and the cutoff test function
`uPark n w R` (for even `w`) are even, which is what allows the *even* whole-space Poincaré
inequality to be applied. -/

lemma cut_neg (n : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) : cut n R (-x) = cut n R x := by
  rw [cut, cut, smul_neg]
  exact ContDiffBump.neg (gbump n) (R⁻¹ • x)

lemma uPark_neg (n : ℕ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ)
    (hweven : ∀ x, w (-x) = w x) (x : EuclideanSpace ℝ (Fin n)) :
    uPark n w R (-x) = uPark n w R x := by
  rw [uPark, uPark, cut_neg, hweven]

/-- Set integrals are invariant under `x ↦ -x` when the set is symmetric. -/
lemma setIntegral_neg_eq_self {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hAm : MeasurableSet A)
    (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ y in A, h (-y)) = ∫ y in A, h y := by
  rw [← integral_indicator hAm, ← integral_indicator hAm]
  rw [show (∫ y, A.indicator (fun y => h (-y)) y) = ∫ y, A.indicator h (-y) from by
    congr 1; funext y; by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hsym y).mp hy)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro hcon
      exact hy (by simpa using (hsym (-y)).mp hcon)]
  rw [integral_neg_eq_self]

lemma penLaplace_neg (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (hAm : MeasurableSet A) (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    penLaplace n A ε (-x) = penLaplace n A ε x := by
  rw [penLaplace, penLaplace]
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖-x - y‖ ^ 2 / ε ^ 2))
      = fun y => Real.exp (-‖x - (-y)‖ ^ 2 / ε ^ 2) from by
    funext y
    have hab : -x - y = -(x - (-y)) := by abel
    rw [hab, norm_neg]]
  exact setIntegral_neg_eq_self hAm hsym (fun y => Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))

lemma penRatio_neg (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (hAm : MeasurableSet A) (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    penRatio n A ε (-x) = penRatio n A ε x := by
  rw [penRatio, penRatio, penLaplace_neg n A ε hAm hsym x]

lemma penG_neg (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (hAm : MeasurableSet A) (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    penG n A ε (-x) = penG n A ε x := by
  rw [penG, penG, penLaplace_neg n A ε hAm hsym x]

lemma penPot_neg (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (hAm : MeasurableSet A) (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    penPot n A ε (-x) = penPot n A ε x := by
  rw [penPot, penPot, penRatio_neg n A ε hAm hsym x]

lemma penF_neg (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (hAm : MeasurableSet A) (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    penF n A ε (-x) = penF n A ε x := by
  rw [penF, penF, norm_neg, penPot_neg n A ε hAm hsym x]

/-! ### The `ε → 0⁺` limit of the penalised quantities

These are the two limits needed for the truncation argument: the weighted variance with respect to
`exp (-(penF n A ε ·))` and its Dirichlet energy both tend, as `ε → 0⁺`, to the corresponding
quantity for the Gaussian restricted to `A`. -/

lemma tendsto_penF_pair (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (hZ : 0 < ∫ x in A, gDens n x)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hCd : ContDiff ℝ 1 u)
    (hCu : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C ∧ ‖fderiv ℝ u x‖ ≤ C) :
    (Tendsto (fun ε : ℝ => wVar (fun x => Real.exp (-(penF n A ε x))) u) (𝓝[>] (0:ℝ))
        (𝓝 ((∫ x in A, u x ^ 2 * gDens n x)
          - (∫ x in A, u x * gDens n x) ^ 2 / (∫ x in A, gDens n x))))
    ∧ (Tendsto (fun ε : ℝ => ∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(penF n A ε x)))
        (𝓝[>] (0:ℝ)) (𝓝 (∫ x in A, ‖fderiv ℝ u x‖ ^ 2 * gDens n x))) := by
  obtain ⟨Cu, hCu0, hCu⟩ := hCu
  set Z : ℝ := ∫ x in A, gDens n x with hZdef
  have hZpos : 0 < Z := hZ
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hgint : Integrable (gDens n) volume := integrable_gDens n
  have hmeas_u : AEStronglyMeasurable u volume :=
    hCd.continuous.measurable.aestronglyMeasurable
  have hphi2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖u x ^ 2‖ * gDens n x) volume :=
    integrable_norm_mul_gDens n (hmeas_u.pow 2) (C := Cu ^ 2) (fun x => by
      have h := (hCu x).1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u x))]
      nlinarith [h, hCu0, abs_nonneg (u x), sq_abs (u x)])
  have hphi1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖u x‖ * gDens n x) volume :=
    integrable_norm_mul_gDens n hmeas_u (C := Cu) (fun x => by
      rw [Real.norm_eq_abs]; exact (hCu x).1)
  have hphi0 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖(1:ℝ)‖ * gDens n x) volume := by
    simpa using hgint
  have hphiD : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖‖fderiv ℝ u x‖ ^ 2‖ * gDens n x) volume :=
    integrable_norm_mul_gDens n (((hCd.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
      (C := Cu ^ 2) (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := (hCu x).2
        nlinarith [h, hCu0, norm_nonneg (fderiv ℝ u x)])
  have hA2 := tendsto_integral_penF_mul n A hA hAm hvol (fun x => u x ^ 2) (hmeas_u.pow 2) hphi2
  have hA1 := tendsto_integral_penF_mul n A hA hAm hvol (fun x => u x) hmeas_u hphi1
  have hA0 : Tendsto (fun ε : ℝ => ∫ x, Real.exp (-(penF n A ε x))) (𝓝[>] (0:ℝ)) (𝓝 Z) := by
    have h := tendsto_integral_penF_mul n A hA hAm hvol (fun _ => (1:ℝ))
      aestronglyMeasurable_const hphi0
    simpa only [one_mul, ← hZdef] using h
  have hAe := tendsto_integral_penF_mul n A hA hAm hvol (fun x => ‖fderiv ℝ u x‖ ^ 2)
    (((hCd.continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable) hphiD
  refine ⟨?_, hAe⟩
  have hvar : Tendsto (fun ε : ℝ => wVar (fun x => Real.exp (-(penF n A ε x))) u)
      (𝓝[>] (0:ℝ))
      (𝓝 ((∫ x in A, u x ^ 2 * gDens n x) - (∫ x in A, u x * gDens n x) ^ 2 / Z)) := by
    have h := hA2.sub ((hA1.pow 2).div hA0 hZne)
    simpa only [wVar, one_mul, ← hZdef, div_apply, Pi.div_apply] using h
  rwa [hZdef] at hvar

/-! ### The cutoff stage, with the sharp even constant -/

lemma bl_cut_stage_even (H : EvenPoincareSmooth)
    (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (hZ : 0 < ∫ x in A, gDens n x)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w) (hweven : ∀ x, w (-x) = w x)
    {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in A, uPark n w R x ^ 2 * gDens n x)
      - (∫ x in A, uPark n w R x * gDens n x) ^ 2 / (∫ x in A, gDens n x)
    ≤ (1 / (4 * Real.pi)) * ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x := by
  obtain ⟨Cu, hCu0, hCu⟩ := bound_uPark n w hw (lt_of_lt_of_le one_pos hR)
  set u : EuclideanSpace ℝ (Fin n) → ℝ := uPark n w R with hu
  have hCd : ContDiff ℝ 1 u := by rw [hu]; exact contDiff_uPark n w hw R
  have hCu' : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C ∧ ‖fderiv ℝ u x‖ ≤ C :=
    ⟨Cu, hCu0, fun x => by rw [hu]; exact hCu x⟩
  obtain ⟨hvar, henergy⟩ := tendsto_penF_pair n A hA hAm hvol hZ u hCd hCu'
  refine le_of_tendsto_of_tendsto hvar (henergy.const_mul (1 / (4 * Real.pi))) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hCd2 : ContDiff ℝ 2 (penF n A ε) := contDiff_penF n hε A hAm hvol
  have hH : ∀ x v : EuclideanSpace ℝ (Fin n),
      2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (penF n A ε)) x v v :=
    hessian_penF n hε A hAm hA hvol
  have hconv : ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) => penF n A ε x - Real.pi * ‖x‖ ^ 2) :=
    convexOn_penF n hε A hAm hA hvol
  have hevenF : ∀ x : EuclideanSpace ℝ (Fin n), penF n A ε (-x) = penF n A ε x :=
    fun x => penF_neg n A ε hAm hsym x
  have hgroF := growth_penF n hε A hAm hA hvol
  have hgroU : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ := by
    rw [hu]; exact growth_uPark n w hw (lt_of_lt_of_le one_pos hR)
  have hu_even : ∀ x : EuclideanSpace ℝ (Fin n), u (-x) = u x := by
    rw [hu]; exact fun x => uPark_neg n w R hweven x
  have hres := H n (penF n A ε) u hCd2 hH hconv hevenF hgroF hCd hu_even hgroU
  simpa only [wVar] using hres

/-! ### The `R → ∞` (cutoff removal) stage -/

lemma bl_final_even (H : EvenPoincareSmooth)
    (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : Convex ℝ A)
    (hsym : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ A ↔ -x ∈ A)
    (hAm : MeasurableSet A) (hvol : 0 < volume A) (hZ : 0 < ∫ x in A, gDens n x)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 1 w) (hweven : ∀ x, w (-x) = w x)
    (hw2 : Integrable (fun x => w x ^ 2 * gDens n x) (volume.restrict A))
    (hg : Integrable (fun x => ‖fderiv ℝ w x‖ ^ 2 * gDens n x) (volume.restrict A))
    (hmean : (∫ x in A, w x * gDens n x) = 0) :
    (∫ x in A, w x ^ 2 * gDens n x)
      ≤ (1 / (4 * Real.pi)) * ∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x := by
  obtain ⟨Cc, hCc⟩ := exists_bound_fderiv_cut n
  set Z : ℝ := ∫ x in A, gDens n x with hZdef
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hgA : Integrable (gDens n) (volume.restrict A) := (integrable_gDens n).integrableOn
  -- integrability of `|w| * gDens` on `A`
  have hwg : Integrable (fun x => |w x| * gDens n x) (volume.restrict A) := by
    have hG : Integrable (fun x => (w x ^ 2 * gDens n x + gDens n x) / 2)
        (volume.restrict A) := (hw2.add hgA).div_const 2
    refine hG.mono' ?_ ?_
    · exact ((hw.continuous.abs.mul (continuous_gDens n)).measurable).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (gDens_nonneg n x))]
      have hg0 := gDens_nonneg n x
      nlinarith [sq_nonneg (|w x| - 1), sq_abs (w x), hg0]
  -- the integrable domination for the energy term
  have hB : Integrable (fun x => (2 * ‖fderiv ℝ w x‖ ^ 2 + 2 * Cc ^ 2 * w x ^ 2) * gDens n x)
      (volume.restrict A) := by
    have h1 : Integrable (fun x => 2 * (‖fderiv ℝ w x‖ ^ 2 * gDens n x)) (volume.restrict A) :=
      hg.const_mul 2
    have h2 : Integrable (fun x => 2 * Cc ^ 2 * (w x ^ 2 * gDens n x)) (volume.restrict A) :=
      hw2.const_mul (2 * Cc ^ 2)
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  -- the three limits
  have hcut_sq : ∀ R x, ‖uPark n w R x ^ 2‖ ≤ w x ^ 2 := by
    intro R x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), uPark, mul_pow]
    have h3 : |cut n R x| ≤ 1 := by
      rw [abs_of_nonneg (cut_nonneg n R x)]; exact cut_le_one n R x
    have h3' : cut n R x ^ 2 ≤ 1 := by
      nlinarith [h3, abs_nonneg (cut n R x), sq_abs (cut n R x)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h3' (sq_nonneg (w x))
  have hI2 : Tendsto (fun R : ℝ => ∫ x in A, uPark n w R x ^ 2 * gDens n x) atTop
      (𝓝 (∫ x in A, w x ^ 2 * gDens n x)) :=
    tendsto_integral_cut_mul n A (fun R x => uPark n w R x ^ 2) (fun x => w x ^ 2)
      (fun x => w x ^ 2) hw2
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => hcut_sq R x)
      (Filter.Eventually.of_forall fun x => tendsto_uPark_sq n w x)
      (Filter.Eventually.of_forall fun R =>
        ((((contDiff_uPark n w hw R).continuous.pow 2).mul (continuous_gDens n)).measurable).aestronglyMeasurable)
  have hcut_le : ∀ R x, ‖uPark n w R x‖ ≤ |w x| := by
    intro R x
    rw [Real.norm_eq_abs, uPark, abs_mul]
    have h3 : |cut n R x| ≤ 1 := by
      rw [abs_of_nonneg (cut_nonneg n R x)]; exact cut_le_one n R x
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h3 (abs_nonneg (w x))
  have hI1 : Tendsto (fun R : ℝ => ∫ x in A, uPark n w R x * gDens n x) atTop (𝓝 0) := by
    have h := tendsto_integral_cut_mul n A (fun R x => uPark n w R x) w (fun x => |w x|) hwg
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => hcut_le R x)
      (Filter.Eventually.of_forall fun x => tendsto_uPark n w x)
      (Filter.Eventually.of_forall fun R =>
        (((contDiff_uPark n w hw R).continuous.mul (continuous_gDens n)).measurable).aestronglyMeasurable)
    rw [hmean] at h
    exact h
  have hcut_fderiv : ∀ R ≥ (1:ℝ), ∀ x, ‖fderiv ℝ (uPark n w R) x‖
      ≤ ‖fderiv ℝ w x‖ + Cc * |w x| := by
    intro R hR x
    rw [fderiv_uPark n w hw R x]
    have h3 : |cut n R x| ≤ 1 := by
      rw [abs_of_nonneg (cut_nonneg n R x)]; exact cut_le_one n R x
    calc ‖cut n R x • fderiv ℝ w x + w x • fderiv ℝ (cut n R) x‖
        ≤ ‖cut n R x • fderiv ℝ w x‖ + ‖w x • fderiv ℝ (cut n R) x‖ := norm_add_le _ _
      _ = |cut n R x| * ‖fderiv ℝ w x‖ + |w x| * ‖fderiv ℝ (cut n R) x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖fderiv ℝ w x‖ + |w x| * Cc := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hCc R hR x) (abs_nonneg _)
      _ = ‖fderiv ℝ w x‖ + Cc * |w x| := by ring
  have hIe : Tendsto (fun R : ℝ => ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x) atTop
      (𝓝 (∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x)) :=
    tendsto_integral_cut_mul n A (fun R x => ‖fderiv ℝ (uPark n w R) x‖ ^ 2)
      (fun x => ‖fderiv ℝ w x‖ ^ 2)
      (fun x => 2 * ‖fderiv ℝ w x‖ ^ 2 + 2 * Cc ^ 2 * w x ^ 2) hB
      ((eventually_ge_atTop (1:ℝ)).mono fun R hR => Filter.Eventually.of_forall fun x => by
        have hnorm := hcut_fderiv R hR x
        have hCcnn : 0 ≤ Cc := le_trans (norm_nonneg _) (hCc 1 le_rfl x)
        have h1 : ‖fderiv ℝ (uPark n w R) x‖ ^ 2 ≤ (‖fderiv ℝ w x‖ + Cc * |w x|) ^ 2 := by
          have h0 : 0 ≤ ‖fderiv ℝ (uPark n w R) x‖ := norm_nonneg _
          have h1 : 0 ≤ ‖fderiv ℝ w x‖ + Cc * |w x| := by positivity
          nlinarith [hnorm, h0, h1]
        have h2 : (‖fderiv ℝ w x‖ + Cc * |w x|) ^ 2
            ≤ 2 * ‖fderiv ℝ w x‖ ^ 2 + 2 * Cc ^ 2 * w x ^ 2 := by
          nlinarith [sq_abs (w x), sq_nonneg (‖fderiv ℝ w x‖ - Cc * |w x|)]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        linarith)
      (Filter.Eventually.of_forall fun x => tendsto_fderiv_uPark_norm_sq n w hw x)
      (Filter.Eventually.of_forall fun R =>
        ((((contDiff_uPark n w hw R).continuous_fderiv (by norm_num)).norm.pow 2).mul
          (continuous_gDens n)).measurable.aestronglyMeasurable)
  -- the cutoff-stage inequality holds eventually
  have hev : ∀ᶠ R in atTop, (∫ x in A, uPark n w R x ^ 2 * gDens n x)
      - (∫ x in A, uPark n w R x * gDens n x) ^ 2 / Z
      ≤ (1 / (4 * Real.pi)) * ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact bl_cut_stage_even H n A hA hsym hAm hvol hZ w hw hweven hR
  have hL : Tendsto (fun R : ℝ => (∫ x in A, uPark n w R x ^ 2 * gDens n x)
      - (∫ x in A, uPark n w R x * gDens n x) ^ 2 / Z) atTop
      (𝓝 (∫ x in A, w x ^ 2 * gDens n x)) := by
    have h := hI2.sub ((hI1.pow 2).div_const Z)
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, sub_zero] using h
  have hRlim : Tendsto (fun R : ℝ => (1 / (4 * Real.pi)) *
      ∫ x in A, ‖fderiv ℝ (uPark n w R) x‖ ^ 2 * gDens n x) atTop
      (𝓝 ((1 / (4 * Real.pi)) * ∫ x in A, ‖fderiv ℝ w x‖ ^ 2 * gDens n x)) :=
    hIe.const_mul _
  exact le_of_tendsto_of_tendsto hL hRlim hev

/-! ### The truncated even Poincaré inequality, in `gDens` form -/

lemma even_poincare_truncated_gDens (H : EvenPoincareSmooth) {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : Convex ℝ A) (hsym : ∀ x, x ∈ A ↔ -x ∈ A) (hAm : MeasurableSet A)
    (hApos : 0 < ∫ x : EuclideanSpace ℝ (Fin n) in A, gDens n x)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (heven : ∀ x, f (-x) = f x)
    (h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => f x ^ 2 * gDens n x) A)
    (hg : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ f x‖ ^ 2 * gDens n x) A) :
    (∫ x : EuclideanSpace ℝ (Fin n) in A, f x ^ 2 * gDens n x)
        / (∫ x : EuclideanSpace ℝ (Fin n) in A, gDens n x)
      - ((∫ x : EuclideanSpace ℝ (Fin n) in A, f x * gDens n x)
          / (∫ x : EuclideanSpace ℝ (Fin n) in A, gDens n x)) ^ 2
    ≤ (1 / (4 * Real.pi)) *
        ((∫ x : EuclideanSpace ℝ (Fin n) in A, ‖fderiv ℝ f x‖ ^ 2 * gDens n x)
          / (∫ x : EuclideanSpace ℝ (Fin n) in A, gDens n x)) := by
  have hZeq : (∫ x in A, gDens n x) = ∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2) :=
    setIntegral_congr_fun hAm (fun x _ => gDens_eq n x)
  have hvol : 0 < volume A := by
    refine volume_pos_of_integral_pos n A hAm ?_
    rw [← hZeq]; exact hApos
  have hgA : Integrable (gDens n) (volume.restrict A) := (integrable_gDens n).integrableOn
  -- integrability of `f * gDens` on `A`
  have hfg : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f x * gDens n x)
      (volume.restrict A) := by
    have hG : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (f x ^ 2 * gDens n x + gDens n x) / 2) (volume.restrict A) :=
      (h2.add hgA).div_const 2
    refine hG.mono' ?_ ?_
    · exact ((hf.continuous.mul (continuous_gDens n)).measurable).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gDens_nonneg n x)]
      have h0 := gDens_nonneg n x
      nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x), h0, abs_nonneg (f x)]
  set Z : ℝ := ∫ x in A, gDens n x with hZdef
  have hZpos : 0 < Z := hApos
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  set c : ℝ := (∫ x in A, f x * gDens n x) / Z with hcdef
  -- the mean of `w = f - c`
  have hcZ : c * (∫ x in A, gDens n x) = ∫ x in A, f x * gDens n x := by
    rw [hcdef, show (∫ x in A, gDens n x) = Z from hZdef.symm]
    field_simp
  have hmean : (∫ x in A, (f x - c) * gDens n x) = 0 := by
    have hfun : (fun x : EuclideanSpace ℝ (Fin n) => (f x - c) * gDens n x)
        = fun x => f x * gDens n x - c * gDens n x := by
      funext x; ring
    rw [hfun, integral_sub hfg (hgA.const_mul c), integral_const_mul]
    linarith [hcZ]
  -- integrability of `w ^ 2 * gDens` on `A`
  have hw2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (f x - c) ^ 2 * gDens n x) (volume.restrict A) := by
    have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        2 * (f x ^ 2 * gDens n x) + 2 * c ^ 2 * gDens n x) (volume.restrict A) :=
      (h2.const_mul 2).add (hgA.const_mul (2 * c ^ 2))
    refine hdom.mono' ?_ ?_
    · exact (((hf.continuous.sub continuous_const).pow 2).mul
        (continuous_gDens n)).measurable.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gDens_nonneg n x))]
      have h0 := gDens_nonneg n x
      nlinarith [sq_nonneg (f x - c), sq_nonneg (f x + c), sq_nonneg (f x), sq_nonneg c,
        sq_nonneg (f x - c), abs_nonneg (f x), sq_abs (f x)]
  -- integrability of `‖∇w‖² * gDens` on `A`
  have hgw : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (fun y => f y - c) x‖ ^ 2 * gDens n x) (volume.restrict A) := by
    refine hg.congr ?_
    filter_upwards with x
    show ‖fderiv ℝ f x‖ ^ 2 * gDens n x
      = ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => f y - c) x‖ ^ 2 * gDens n x
    rw [fderiv_sub_const c]
  have hw_cd : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => f x - c) :=
    hf.sub contDiff_const
  have hw_even : ∀ x : EuclideanSpace ℝ (Fin n), (fun y => f y - c) (-x) = (fun y => f y - c) x :=
    fun x => by show f (-x) - c = f x - c; rw [heven x]
  have hmain := bl_final_even H n A hA hsym hAm hvol hZpos (fun y => f y - c)
    hw_cd hw_even hw2 hgw hmean
  -- the variance identity
  have hfw : (∫ x in A, ‖fderiv ℝ (fun y => f y - c) x‖ ^ 2 * gDens n x)
      = ∫ x in A, ‖fderiv ℝ f x‖ ^ 2 * gDens n x := by
    refine setIntegral_congr_fun hAm (fun x _ => ?_)
    rw [fderiv_sub_const c]
  rw [hfw] at hmain
  have hA1 : (∫ x in A, (f x - c) ^ 2 * gDens n x)
      = (∫ x in A, f x ^ 2 * gDens n x) - c ^ 2 * Z := by
    have hAB : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        f x ^ 2 * gDens n x - c ^ 2 * gDens n x) (volume.restrict A) := by
      refine (h2.sub (hgA.const_mul (c ^ 2))).congr ?_
      filter_upwards with x
      simp only [Pi.sub_apply]
    have hCD : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (2 * c) * ((f x - c) * gDens n x)) (volume.restrict A) := by
      have hfg' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (f x - c) * gDens n x)
          (volume.restrict A) := by
        refine (hfg.sub (hgA.const_mul c)).congr ?_
        filter_upwards with x
        simp only [Pi.sub_apply]; ring
      exact hfg'.const_mul (2 * c)
    have hc2g : (∫ x in A, c ^ 2 * gDens n x) = c ^ 2 * (∫ x in A, gDens n x) := by
      simpa using integral_const_mul (c ^ 2) (fun x : EuclideanSpace ℝ (Fin n) => gDens n x)
    have h2cg : (∫ x in A, (2 * c) * ((f x - c) * gDens n x))
        = (2 * c) * ∫ x in A, (f x - c) * gDens n x := by
      simpa using integral_const_mul (2 * c)
        (fun x : EuclideanSpace ℝ (Fin n) => (f x - c) * gDens n x)
    have hsub : (∫ x in A, f x ^ 2 * gDens n x - c ^ 2 * gDens n x)
        = (∫ x in A, f x ^ 2 * gDens n x) - ∫ x in A, c ^ 2 * gDens n x := by
      simpa using integral_sub h2 (hgA.const_mul (c ^ 2))
    have hsplit : (∫ x in A, ((f x ^ 2 * gDens n x - c ^ 2 * gDens n x)
            - (2 * c) * ((f x - c) * gDens n x)))
        = (∫ x in A, f x ^ 2 * gDens n x - c ^ 2 * gDens n x)
          - ∫ x in A, (2 * c) * ((f x - c) * gDens n x) := by
      simpa using integral_sub hAB hCD
    have hcongr : (∫ x in A, (f x - c) ^ 2 * gDens n x)
        = ∫ x in A, ((f x ^ 2 * gDens n x - c ^ 2 * gDens n x)
            - (2 * c) * ((f x - c) * gDens n x)) :=
      setIntegral_congr_fun hAm (fun x _ => by ring)
    rw [hcongr, hsplit, hsub, hc2g, h2cg, hmean, hZdef]
    ring
  have hvar_eq : (∫ x in A, f x ^ 2 * gDens n x) / Z - c ^ 2
      = (∫ x in A, (f x - c) ^ 2 * gDens n x) / Z := by
    rw [hA1]; field_simp
  rw [hvar_eq]
  have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hZpos)
  calc (∫ x in A, (f x - c) ^ 2 * gDens n x) / Z
      ≤ ((1 / (4 * Real.pi)) * ∫ x in A, ‖fderiv ℝ f x‖ ^ 2 * gDens n x) / Z := hdiv
    _ = (1 / (4 * Real.pi)) *
        ((∫ x in A, ‖fderiv ℝ f x‖ ^ 2 * gDens n x) / Z) := by ring

/-- **Even Poincaré inequality for the Gaussian truncated to a symmetric convex set, reduced to the
whole-space smooth case.**

`H` is the whole-space "even Poincaré for a `C²` even `2π`-strongly convex potential" statement
(cf. `Commons.Analysis.GaussianMeasure.even_poincare_smooth`).  The conclusion is the even Poincaré
inequality for the Gaussian truncated to a symmetric convex `A`.

The proof is the truncation/penalty argument of `bl_cut_stage`/`bl_final` in
`Submission/Commons/Analysis/GaussianMeasure/brascamp_lieb_truncated.lean`, using that for symmetric
`A` the penalty `penPot n A ε` is even and the cutoff `cut n R` is radial (hence even), so that `H`
applies. -/
theorem even_poincare_truncated_of_smooth
    (H : ∀ (m : ℕ) (g h : EuclideanSpace ℝ (Fin m) → ℝ),
        ContDiff ℝ 2 g →
        (∀ x v : EuclideanSpace ℝ (Fin m), 2 * Real.pi * ‖v‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ g) x v v) →
        ConvexOn ℝ Set.univ (fun x => g x - Real.pi * ‖x‖ ^ 2) →
        (∀ x : EuclideanSpace ℝ (Fin m), g (-x) = g x) →
        (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin m),
          |fderiv ℝ g x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
          |fderiv ℝ (fderiv ℝ g) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) →
        ContDiff ℝ 1 h →
        (∀ x : EuclideanSpace ℝ (Fin m), h (-x) = h x) →
        (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin m),
          |h x| ≤ C * (1 + ‖x‖) ^ N ∧
          |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) →
        (∫ x, h x ^ 2 * Real.exp (-(g x)))
            - (∫ x, h x * Real.exp (-(g x))) ^ 2 / (∫ x, Real.exp (-(g x)))
          ≤ (1 / (4 * Real.pi)) * ∫ x, ‖fderiv ℝ h x‖ ^ 2 * Real.exp (-(g x)))
    {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : Convex ℝ A) (hsym : ∀ x, x ∈ A ↔ -x ∈ A) (hAm : MeasurableSet A)
    (hApos : 0 < ∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (heven : ∀ x, f (-x) = f x)
    (h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A)
    (hg : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) A) :
    (∫ x : EuclideanSpace ℝ (Fin n) in A, f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
        / (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
      - ((∫ x : EuclideanSpace ℝ (Fin n) in A, f x * Real.exp (-Real.pi * ‖x‖ ^ 2))
          / (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))) ^ 2
    ≤ (1 / (4 * Real.pi)) *
        ((∫ x : EuclideanSpace ℝ (Fin n) in A,
            ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
          / (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))) := by
  have heq2 : (fun x : EuclideanSpace ℝ (Fin n) => f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => f x ^ 2 * gDens n x := by funext x; rw [gDens_eq]
  have heqm : (fun x : EuclideanSpace ℝ (Fin n) => f x * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => f x * gDens n x := by funext x; rw [gDens_eq]
  have heqD : (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => ‖fderiv ℝ f x‖ ^ 2 * gDens n x := by funext x; rw [gDens_eq]
  have heqZ : (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => gDens n x := by funext x; rw [gDens_eq]
  have h2' : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => f x ^ 2 * gDens n x) A :=
    h2.congr (Filter.Eventually.of_forall fun x => congrFun heq2 x)
  have hg' : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ f x‖ ^ 2 * gDens n x) A :=
    hg.congr (Filter.Eventually.of_forall fun x => congrFun heqD x)
  have hZpos : 0 < ∫ x : EuclideanSpace ℝ (Fin n) in A, gDens n x := by
    rw [← setIntegral_congr_fun hAm (fun x _ => congrFun heqZ x)]
    exact hApos
  have key := even_poincare_truncated_gDens H A hA hsym hAm hZpos f hf heven h2' hg'
  have hc2 : (∫ x : EuclideanSpace ℝ (Fin n) in A, f x ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in A, f x ^ 2 * gDens n x :=
    setIntegral_congr_fun hAm (fun x _ => congrFun heq2 x)
  have hcm : (∫ x : EuclideanSpace ℝ (Fin n) in A, f x * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in A, f x * gDens n x :=
    setIntegral_congr_fun hAm (fun x _ => congrFun heqm x)
  have hcZ : (∫ x : EuclideanSpace ℝ (Fin n) in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in A, gDens n x :=
    setIntegral_congr_fun hAm (fun x _ => congrFun heqZ x)
  have hcD : (∫ x : EuclideanSpace ℝ (Fin n) in A,
        ‖fderiv ℝ f x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in A, ‖fderiv ℝ f x‖ ^ 2 * gDens n x :=
    setIntegral_congr_fun hAm (fun x _ => congrFun heqD x)
  rw [hc2, hcm, hcZ, hcD]
  exact key

end

end Commons.Analysis.GaussianMeasure
