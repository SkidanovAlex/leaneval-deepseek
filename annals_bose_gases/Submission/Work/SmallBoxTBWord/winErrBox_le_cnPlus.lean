import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The window-derivative error is dominated by the box excited count

For the box mean-free projection `Q_{B,i} = boxQ volA A i` and the
window-derivative weight `∑_k (∂_kχ)²`, the trivial pointwise bound

    (∑_k (∂_kχ)(x_i)²) · (Q_{B,i}Ψ x)²  ≤  B · (Q_{B,i}Ψ x)²

(valid because `∑_k (∂_kχ)²` is a sum of squares, hence `≤ B`, and because
`(Q_{B,i}Ψ x)² ≥ 0`) integrates to

    winErrBox a A volA χ Ψ ≤ B · cnPlusBox a A volA Ψ .

The only work is to make the two integrals comparable: the right-hand
integrand `B · (Q_{B,i}Ψ)²` must be *integrable* over the box.  That is a
consequence of the compactness hypotheses: the box mean `boxP volA A i Ψ` is a
mean of `Ψ` over the compact set `A` evaluated along the compact image
`{(x_{i←z}) | x ∈ abox N a, z ∈ A}`, so it is bounded on `abox N a`; and it is
strongly measurable in `x` (`StronglyMeasurable.integral_prod_right'`, which
needs no integrability).  Note that neither smoothness of `χ` nor
integrability of `Q_{B,i}Ψ` is assumed: the whole estimate is genuinely
elementary.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Strong measurability of the box mean and the mean-free projection -/

/-- The box mean `boxP volA A i Ψ` is strongly measurable in `x`, for `Ψ` merely
continuous (`StronglyMeasurable.integral_prod_right'` needs no integrability). -/
lemma boxP_stronglyMeasurable {A : Set ℝ³} (volA : ℝ) {N : ℕ} (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    StronglyMeasurable (boxP volA A i Ψ) := by
  have hjoint : StronglyMeasurable
      (fun p : X N × ℝ³ => Ψ (Function.update p.1 i p.2)) :=
    (hΨ.comp (by fun_prop : Continuous (fun p : X N × ℝ³ => Function.update p.1 i p.2))).stronglyMeasurable
  have hI : StronglyMeasurable
      (fun x : X N => ∫ z : ℝ³, Ψ (Function.update x i z) ∂((volume : Measure ℝ³).restrict A)) :=
    hjoint.integral_prod_right'
  unfold boxP
  exact hI.const_mul (1 / volA)

/-- The mean-free projection `boxQ volA A i Ψ` is strongly measurable. -/
lemma boxQ_stronglyMeasurable {A : Set ℝ³} (volA : ℝ) {N : ℕ} (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    StronglyMeasurable (boxQ volA A i Ψ) := by
  unfold boxQ
  exact hΨ.stronglyMeasurable.sub (boxP_stronglyMeasurable volA i hΨ)

/-! ## Boundedness of the mean-free projection on the box -/

/-- On the ambient box, `boxQ volA A i Ψ` is bounded, because the box mean is a
mean of the continuous `Ψ` over the compact set `A` along the compact image of
`abox N a × A` under the slot update. -/
lemma boxQ_le_bound {a : ℝ} {A : Set ℝ³} {volA : ℝ} {N : ℕ} (ha : 0 < a)
    (hA : IsCompact A) (i : Fin N) {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ abox N a, |boxQ volA A i Ψ x| ≤ K := by
  set S : Set (X N) :=
    abox N a ∪ (fun p : X N × ℝ³ => Function.update p.1 i p.2) '' (abox N a ×ˢ A)
    with hSdef
  have hS : IsCompact S := by
    refine (abox_compact N ha).union ?_
    exact ((abox_compact N ha).prod hA).image
      (by fun_prop : Continuous (fun p : X N × ℝ³ => Function.update p.1 i p.2))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hΨ.continuousOn
  have hM0 : 0 ≤ M := by
    have h0 : ‖Ψ (0 : X N)‖ ≤ M :=
      hM 0 (by rw [hSdef]; exact Or.inl (zero_mem_abox ha.le))
    exact le_trans (norm_nonneg _) h0
  have hmem : ∀ x ∈ abox N a, ∀ z ∈ A, Function.update x i z ∈ S := by
    intro x hx z hz
    rw [hSdef]
    exact Or.inr ⟨(x, z), ⟨hx, hz⟩, rfl⟩
  refine ⟨M + |1 / volA| * (M * ((volume : Measure ℝ³) A).toReal), ?_, ?_⟩
  · exact add_nonneg hM0
      (mul_nonneg (abs_nonneg _) (mul_nonneg hM0 ENNReal.toReal_nonneg))
  · intro x hx
    have hΨx : |Ψ x| ≤ M := by
      have h := hM x (by rw [hSdef]; exact Or.inl hx)
      simpa [Real.norm_eq_abs] using h
    have hI : ‖∫ z in A, Ψ (Function.update x i z)‖ ≤ M * ((volume : Measure ℝ³) A).toReal := by
      haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict A) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hA.measure_lt_top⟩
      have hb : ∀ᵐ z ∂((volume : Measure ℝ³).restrict A), ‖Ψ (Function.update x i z)‖ ≤ M := by
        rw [ae_restrict_iff' hA.isClosed.measurableSet]
        exact ae_of_all volume (fun z hz => hM (Function.update x i z) (hmem x hx z hz))
      have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure ℝ³).restrict A)
        (f := fun z : ℝ³ => Ψ (Function.update x i z)) (C := M) hb
      simpa [measureReal_def, Measure.restrict_apply_univ] using h
    have hI' : |∫ z in A, Ψ (Function.update x i z)| ≤ M * ((volume : Measure ℝ³) A).toReal := by
      simpa [Real.norm_eq_abs] using hI
    have hboxP : |boxP volA A i Ψ x|
        ≤ |1 / volA| * (M * ((volume : Measure ℝ³) A).toReal) := by
      unfold boxP
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hI' (abs_nonneg _)
    calc |boxQ volA A i Ψ x| = |Ψ x - boxP volA A i Ψ x| := rfl
      _ ≤ |Ψ x| + |boxP volA A i Ψ x| := by
            simpa [Real.norm_eq_abs] using norm_sub_le (Ψ x) (boxP volA A i Ψ x)
      _ ≤ M + |1 / volA| * (M * ((volume : Measure ℝ³) A).toReal) := add_le_add hΨx hboxP

/-! ## Integrability of the squared mean-free projection -/

/-- `(Q_{B,i}Ψ)²` is integrable over the ambient box, for `Ψ` merely
continuous. -/
lemma integrableOn_sq_boxQ {a : ℝ} {A : Set ℝ³} {volA : ℝ} {N : ℕ} (ha : 0 < a)
    (hA : IsCompact A) (i : Fin N) {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    IntegrableOn (fun x : X N => (boxQ volA A i Ψ x) ^ 2) (abox N a) := by
  obtain ⟨K, hK0, hK⟩ := boxQ_le_bound ha hA i hΨ
  refine IntegrableOn.of_bound (abox_compact N ha).measure_lt_top ?_ (K ^ 2) ?_
  · have hq : AEStronglyMeasurable (fun x : X N => boxQ volA A i Ψ x)
        (volume.restrict (abox N a)) :=
      (boxQ_stronglyMeasurable volA i hΨ).aestronglyMeasurable
    exact hq.pow 2
  · rw [ae_restrict_iff' (abox_measurable N a)]
    exact ae_of_all volume (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK x hx) 2)

/-! ## The main estimate -/

theorem winErrBox_le_cnPlus {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA B : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ} (ha : 0 < a) (hA : IsCompact A) (hB0 : 0 ≤ B) (hB : ∀ x : EuclideanSpace ℝ (Fin 3), (∑ k : Fin 3, (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ B) (hΨ : Continuous Ψ) : Work.SmallBoxTBWord.winErrBox a A volA χ Ψ ≤ B * Work.SmallBoxTBWord.cnPlusBox a A volA Ψ := by
  unfold winErrBox cnPlusBox
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  calc ∫ x in abox N a,
        (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2) * (boxQ volA A i Ψ x) ^ 2
      ≤ ∫ x in abox N a, B * (boxQ volA A i Ψ x) ^ 2 := by
        refine integral_mono_of_nonneg
          (Eventually.of_forall (fun x => ?_)) ?_ (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (sq_nonneg _)
        · have hq : Integrable (fun x : X N => (boxQ volA A i Ψ x) ^ 2)
              (volume.restrict (abox N a)) := integrableOn_sq_boxQ ha hA i hΨ
          exact hq.const_mul B
        · exact mul_le_mul_of_nonneg_right (hB (x i)) (sq_nonneg _)
    _ = B * ∫ x in abox N a, (boxQ volA A i Ψ x) ^ 2 :=
        integral_const_mul B (fun x : X N => (boxQ volA A i Ψ x) ^ 2)

end Work.SmallBoxTBWord
