import Mathlib
import Submission.Commons.Analysis.Integral.riesz_thorin_finite

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

noncomputable section

/-! ## Extending a function on a finite subset of `ℤ` by zero -/

/-- Extend a function on a finset `S : Finset ℤ` by zero to a finitely supported function
on `ℤ`. -/
noncomputable def extendZeroLM (S : Finset ℤ) : (↥S → ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) where
  toFun g := Finsupp.embDomain (Function.Embedding.subtype (fun n : ℤ => n ∈ S))
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ ↥S).symm g)
  map_add' g h := by
    simp only [map_add, Finsupp.embDomain_add]
  map_smul' c g := by
    simp only [map_smul, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_smul,
      RingHom.id_apply]

lemma extendZeroLM_apply (S : Finset ℤ) (g : ↥S → ℂ) (n : ℤ) :
    extendZeroLM S g n = if h : n ∈ S then g ⟨n, h⟩ else 0 := by
  change Finsupp.embDomain (Function.Embedding.subtype (fun m : ℤ => m ∈ S))
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ ↥S).symm g) n
      = if h : n ∈ S then g ⟨n, h⟩ else 0
  rw [Finsupp.embDomain_apply]
  by_cases hn : n ∈ S
  · have hcho : (⟨⟨n, hn⟩, rfl⟩ : ∃ a : ↥S,
        (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n).choose = ⟨n, hn⟩ :=
      Subtype.ext (Exists.choose_spec (⟨⟨n, hn⟩, rfl⟩ : ∃ a : ↥S,
        (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n))
    rw [dif_pos ⟨⟨n, hn⟩, rfl⟩, dif_pos hn, hcho]
    exact congrFun (Finsupp.linearEquivFunOnFinite_symm_apply ℂ ℂ ↥S g) ⟨n, hn⟩
  · have hno : ¬ ∃ a : ↥S, (Function.Embedding.subtype (fun m : ℤ => m ∈ S)) a = n := by
      rintro ⟨a, ha⟩
      exact hn (ha ▸ a.2)
    rw [dif_neg hno, dif_neg hn]

lemma extendZeroLM_self (f : ℤ →₀ ℂ) : extendZeroLM f.support (fun a => f a) = f := by
  ext n
  simp only [extendZeroLM_apply]
  by_cases hn : n ∈ f.support
  · rw [dif_pos hn]
  · rw [dif_neg hn]; exact (Finsupp.notMem_support_iff.mp hn).symm

lemma tsum_norm_extendZeroLM (S : Finset ℤ) (g : ↥S → ℂ) {q : ℝ} (hq : 0 < q) :
    (∑' n : ℤ, ‖extendZeroLM S g n‖ ^ q) = ∑ a : ↥S, ‖g a‖ ^ q := by
  rw [tsum_eq_sum (s := S) (f := fun n : ℤ => ‖extendZeroLM S g n‖ ^ q)]
  · rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun n => ‖extendZeroLM S g n‖ ^ q)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [extendZeroLM_apply, dif_pos a.2]
  · intro n hn
    rw [extendZeroLM_apply, dif_neg hn, norm_zero, Real.zero_rpow (ne_of_gt hq)]

/-! ## `eLpNorm` on `ℤ` with counting measure -/

/-- `eLpNorm` against the counting measure on `ℤ` as a (possibly infinite) `ℓ^q` sum. -/
lemma eLpNorm_count_eq_tsum (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) ^ (1 / q) := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    (measurable_of_countable f).aestronglyMeasurable,
    MeasureTheory.eLpNorm', ENNReal.toReal_ofReal hq.le, MeasureTheory.lintegral_count]
  congr 1
  apply tsum_congr
  intro n
  rw [show ‖f n‖ₑ = ENNReal.ofReal ‖f n‖ by simp [enorm_eq_nnnorm],
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]

/-- For a function supported in a finite window, the `eLpNorm` against the counting measure is the
`ofReal` of the finite `ℓ^q` sum. -/
lemma eLpNorm_count_eq_ofReal_sum {f : ℤ → ℂ} {W : Finset ℤ} (hf : ∀ n, n ∉ W → f n = 0)
    {q : ℝ} (hq : 0 < q) :
    eLpNorm f (ENNReal.ofReal q) Measure.count
      = ENNReal.ofReal ((∑ n ∈ W, ‖f n‖ ^ q) ^ (1 / q)) := by
  rw [eLpNorm_count_eq_tsum f hq]
  have h : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) = ∑ n ∈ W, ENNReal.ofReal (‖f n‖ ^ q) :=
    tsum_eq_sum (fun n hn => by
      rw [hf n hn, norm_zero, Real.zero_rpow (ne_of_gt hq), ENNReal.ofReal_zero])
  rw [h, ← ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) q)]
  exact ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) q) (by positivity)

/-- The reverse comparison: a finite `ℓ^q` sum over a window is dominated by the `eLpNorm`. -/
lemma ofReal_sum_le_eLpNorm_count (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) (F : Finset ℤ) :
    ENNReal.ofReal ((∑ n ∈ F, ‖f n‖ ^ q) ^ (1 / q))
      ≤ eLpNorm f (ENNReal.ofReal q) Measure.count := by
  rw [eLpNorm_count_eq_tsum f hq, ← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun n _ => Real.rpow_nonneg (norm_nonneg _) q) (by positivity : (0:ℝ) ≤ 1/q)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) q)]
  exact ENNReal.sum_le_tsum F

/-! ## The finite-`F` reduction -/

/-- The finite-`F` restriction of the operator: `g ↦ (b ↦ T (extendZeroLM S g) b)`. -/
noncomputable def restrictLM (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (S : Finset ℤ) (F : Finset ℤ) :
    (↥S → ℂ) →ₗ[ℂ] (↥F → ℂ) where
  toFun g b := T (extendZeroLM S g) b
  map_add' g h := by funext b; simp
  map_smul' c g := by funext b; simp

@[simp] lemma restrictLM_apply (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (S F : Finset ℤ)
    (g : ↥S → ℂ) (b : ↥F) : restrictLM T S F g b = T (extendZeroLM S g) b := rfl

/-- Transfer of a single `eLpNorm` endpoint bound to the finite type `↥S`: a finite `ℓ^q`-sum over
a window `F` of `T (extendZeroLM S g)` is bounded by `M` times the finite `ℓ^q`-sum of `g`. -/
private lemma endpoint_bound {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (hT : ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal q) Measure.count)
    (S : Finset ℤ) (g : ↥S → ℂ) (F : Finset ℤ) :
    (∑ b ∈ F, ‖T (extendZeroLM S g) b‖ ^ q) ^ (1 / q)
      ≤ M * (∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q) := by
  have he := hT (extendZeroLM S g)
  have hlow := ofReal_sum_le_eLpNorm_count (T (extendZeroLM S g)) hq F
  have hup : eLpNorm (extendZeroLM S g) (ENNReal.ofReal q) Measure.count
      = ENNReal.ofReal ((∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q)) := by
    rw [eLpNorm_count_eq_ofReal_sum (f := extendZeroLM S g) (W := S)
      (fun n hn => by rw [extendZeroLM_apply, dif_neg hn]) hq]
    have hs : (∑ n ∈ S, ‖extendZeroLM S g n‖ ^ q) = ∑ a : ↥S, ‖g a‖ ^ q := by
      rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun n => ‖extendZeroLM S g n‖ ^ q)]
      exact Finset.sum_congr rfl (fun a _ => by rw [extendZeroLM_apply, dif_pos a.2])
    rw [hs]
  have h1 : ENNReal.ofReal ((∑ b ∈ F, ‖T (extendZeroLM S g) b‖ ^ q) ^ (1 / q))
      ≤ ENNReal.ofReal M * ENNReal.ofReal ((∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q)) :=
    calc ENNReal.ofReal ((∑ b ∈ F, ‖T (extendZeroLM S g) b‖ ^ q) ^ (1 / q))
        ≤ eLpNorm (T (extendZeroLM S g)) (ENNReal.ofReal q) Measure.count := hlow
      _ ≤ ENNReal.ofReal M * eLpNorm (extendZeroLM S g) (ENNReal.ofReal q) Measure.count := he
      _ = ENNReal.ofReal M * ENNReal.ofReal ((∑ a : ↥S, ‖g a‖ ^ q) ^ (1 / q)) := by rw [hup]
  rw [← ENNReal.ofReal_mul hM] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hM (Real.rpow_nonneg
      (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) q)) _))).mp h1

/-- **The finite-`F` reduction.**  For every `f : ℤ →₀ ℂ` and every finite `F ⊆ ℤ`, the part of the
`ℓ^p` norm of `T f` sitting on `F` obeys the interpolated bound.  This is the reduction of the
infinite `ℤ`-sums to the finite-type Riesz–Thorin theorem
`Commons.Analysis.Integral.riesz_thorin_finite` (source `↥f.support`, target `↥F`). -/
private lemma finite_F_bound {q₀ q₁ p θ A B : ℝ} (h0 : 1 ≤ q₀) (h1 : q₀ ≤ q₁)
    (hp : 1 < p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθp : 1 / p = (1 - θ) / q₀ + θ / q₁)
    (hA : 0 < A) (hB : 0 < B)
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (hT0 : ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal q₀) Measure.count
        ≤ ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal q₀) Measure.count)
    (hT1 : ∀ f : ℤ →₀ ℂ, eLpNorm (T f) (ENNReal.ofReal q₁) Measure.count
        ≤ ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal q₁) Measure.count)
    (f : ℤ →₀ ℂ) (F : Finset ℤ) :
    (∑ n ∈ F, ‖T f n‖ ^ p) ^ (1 / p)
      ≤ A ^ (1 - θ) * B ^ θ * (∑ n ∈ f.support, ‖f n‖ ^ p) ^ (1 / p) := by
  classical
  have hq0 : 0 < q₀ := lt_of_lt_of_le zero_lt_one h0
  have hq1 : 1 ≤ q₁ := le_trans h0 h1
  have hq1pos : 0 < q₁ := lt_of_lt_of_le zero_lt_one hq1
  have hT0' : ∀ g : ↥f.support → ℂ,
      (∑ b : ↥F, ‖restrictLM T f.support F g b‖ ^ q₀) ^ (1 / q₀)
        ≤ A * (∑ a : ↥f.support, ‖g a‖ ^ q₀) ^ (1 / q₀) := by
    intro g
    simp only [restrictLM_apply]
    rw [← Finset.sum_subtype F (fun x => Iff.rfl)
      (fun n => ‖T (extendZeroLM f.support g) n‖ ^ q₀)]
    exact endpoint_bound hq0 hA.le T hT0 f.support g F
  have hT1' : ∀ g : ↥f.support → ℂ,
      (∑ b : ↥F, ‖restrictLM T f.support F g b‖ ^ q₁) ^ (1 / q₁)
        ≤ B * (∑ a : ↥f.support, ‖g a‖ ^ q₁) ^ (1 / q₁) := by
    intro g
    simp only [restrictLM_apply]
    rw [← Finset.sum_subtype F (fun x => Iff.rfl)
      (fun n => ‖T (extendZeroLM f.support g) n‖ ^ q₁)]
    exact endpoint_bound hq1pos hB.le T hT1 f.support g F
  have hθp' : p⁻¹ = (1 - θ) * q₀⁻¹ + θ * q₁⁻¹ := by
    rw [one_div, div_eq_mul_inv, div_eq_mul_inv] at hθp
    exact hθp
  have hmain := Commons.Analysis.Integral.riesz_thorin_finite (α := ↥f.support) (β := ↥F)
    (restrictLM T f.support F) (p0 := q₀) (p1 := q₁) (q0 := q₀) (q1 := q₁)
    (M0 := A) (M1 := B) (pθ := p) (qθ := p)
    h0 hq1 h0 hq1 hA.le hB.le hT0' hT1' hθ0 hθ1 hp.le hp.le hθp' hθp'
  have hres := hmain (fun a : ↥f.support => f a)
  have hL : (∑ b : ↥F, ‖restrictLM T f.support F (fun a : ↥f.support => f a) b‖ ^ p)
      = ∑ n ∈ F, ‖T f n‖ ^ p := by
    simp only [restrictLM_apply, extendZeroLM_self]
    rw [← Finset.sum_subtype F (fun x => Iff.rfl) (fun n => ‖T f n‖ ^ p)]
  have hR : (∑ a : ↥f.support, ‖(fun a : ↥f.support => f a) a‖ ^ p)
      = ∑ n ∈ f.support, ‖f n‖ ^ p := by
    rw [← Finset.sum_subtype f.support (fun x => Iff.rfl) (fun n => ‖f n‖ ^ p)]
  rw [hL, hR] at hres
  exact hres

/-- Riesz–Thorin (log-convexity of the ℓᵖ operator norm) for `ℤ`-indexed sequences with counting measure, in the `eLpNorm` form used throughout this development: bounds at the two exponents `q₀ ≤ q₁` give the bound at every interpolating exponent `p`.

Reduction plan: `riesz_thorin_finite` (in `Submission/Commons/Analysis/Integral/riesz_thorin_finite.lean`) is the finite-type case with *different* source and target exponents `p_i`, `q_i`; get the diagonal case from it by restricting the source to `↥f.support` and the target to a finite `F ⊆ ℤ` (the linear map `g ↦ (fun b : ↥F => T (extendZeroLM f.support g) b)`, cf. `Work.BourgainPlan.IonescuWainger.ellp_finite_F_bound`), then take the supremum over `F` (the `ℤ`-count `eLpNorm` is the sup of the `eLpNorm`s of the finite truncations, cf. `Submission/Commons/Analysis/Lp/eLpNorm_eq_iSup_indicator_Icc.lean`). -/
theorem ellp_interpolation {q₀ q₁ p θ A B : ℝ} (h0 : 1 ≤ q₀) (h1 : q₀ ≤ q₁)
    (hp : 1 < p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθp : 1 / p = (1 - θ) / q₀ + θ / q₁)
    (hA : 0 < A) (hB : 0 < B)
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (hT0 : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (T f) (ENNReal.ofReal q₀) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm f (ENNReal.ofReal q₀) MeasureTheory.Measure.count)
    (hT1 : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (T f) (ENNReal.ofReal q₁) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm f (ENNReal.ofReal q₁) MeasureTheory.Measure.count) :
    ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ (1 - θ) * B ^ θ)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  intro f
  classical
  have hppos : 0 < p := lt_trans zero_lt_one hp
  have hDnn : 0 ≤ A ^ (1 - θ) * B ^ θ :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  set S : ℝ := ∑ n ∈ f.support, ‖f n‖ ^ p with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)
  have hfnorm : eLpNorm f (ENNReal.ofReal p) Measure.count = ENNReal.ofReal (S ^ (1 / p)) := by
    rw [hSdef]
    exact eLpNorm_count_eq_ofReal_sum (fun n hn => Finsupp.notMem_support_iff.mp hn) hppos
  have h1pp : (1 / p) * p = 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hppos)]
  have hp1p : p * (1 / p) = 1 := by rw [one_div, mul_inv_cancel₀ (ne_of_gt hppos)]
  have hstep : ∀ F : Finset ℤ, (∑ n ∈ F, ENNReal.ofReal (‖T f n‖ ^ p))
      ≤ ENNReal.ofReal ((A ^ (1 - θ) * B ^ θ) ^ p * S) := by
    intro F
    have hb := finite_F_bound h0 h1 hp hθ0 hθ1 hθp hA hB T hT0 hT1 f F
    rw [← hSdef] at hb
    have hsumnn : 0 ≤ ∑ n ∈ F, ‖T f n‖ ^ p :=
      Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)
    have hpow : (A ^ (1 - θ) * B ^ θ * S ^ (1 / p)) ^ p
        = (A ^ (1 - θ) * B ^ θ) ^ p * S := by
      rw [Real.mul_rpow hDnn (Real.rpow_nonneg hSnn _),
        ← Real.rpow_mul hSnn (1 / p) p, h1pp, Real.rpow_one]
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hsumnn _) hb hppos.le
    rw [← Real.rpow_mul hsumnn (1 / p) p, h1pp, Real.rpow_one, hpow] at h
    calc (∑ n ∈ F, ENNReal.ofReal (‖T f n‖ ^ p))
        = ENNReal.ofReal (∑ n ∈ F, ‖T f n‖ ^ p) :=
          (ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)).symm
      _ ≤ ENNReal.ofReal ((A ^ (1 - θ) * B ^ θ) ^ p * S) := ENNReal.ofReal_le_ofReal h
  rw [eLpNorm_count_eq_tsum (T f) hppos]
  have htsum : (∑' n : ℤ, ENNReal.ofReal (‖T f n‖ ^ p))
      ≤ ENNReal.ofReal ((A ^ (1 - θ) * B ^ θ) ^ p * S) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hstep
  calc (∑' n : ℤ, ENNReal.ofReal (‖T f n‖ ^ p)) ^ (1 / p)
      ≤ (ENNReal.ofReal ((A ^ (1 - θ) * B ^ θ) ^ p * S)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow htsum (by positivity)
    _ = ENNReal.ofReal (((A ^ (1 - θ) * B ^ θ) ^ p * S) ^ (1 / p)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    _ = ENNReal.ofReal (A ^ (1 - θ) * B ^ θ * S ^ (1 / p)) := by
        congr 1
        rw [Real.mul_rpow (Real.rpow_nonneg hDnn p) hSnn,
          ← Real.rpow_mul hDnn p (1 / p), hp1p, Real.rpow_one]
    _ = ENNReal.ofReal (A ^ (1 - θ) * B ^ θ) * ENNReal.ofReal (S ^ (1 / p)) :=
        ENNReal.ofReal_mul hDnn
    _ = ENNReal.ofReal (A ^ (1 - θ) * B ^ θ)
        * eLpNorm f (ENNReal.ofReal p) Measure.count := by rw [hfnorm]

end

end Work.BourgainPlan.Maximal
