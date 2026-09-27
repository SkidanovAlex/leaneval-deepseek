import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.NatMeasure

/-!
# Strict positivity of the second moment of a pushforward of `sigma n` (area N2)

For `φ` a continuous bijection of the boundary sphere `Sph n` and `v ≠ 0`, the second moment

  `∫ ξ, (‖v‖² - ⟪φ ξ, v⟫²) ∂σ`

of the normalised rotation-invariant measure `σ = sigma n` is **strictly** positive.  Equivalently,
the covariance/second-moment operator of the pushed-forward measure on the sphere is strictly
contracting along every non-zero direction (up to the trace normalisation) — the analytic content
of the BCG strict-dominance lemma `HlinStrictMoment`.

The only inputs are the measure-theoretic side conditions on `σ` (probability, carried by the
sphere, atomless), the fact that `φ` maps `Sph n` bijectively onto itself and is continuous there.

The argument is elementary.  The integrand `g ξ = ‖v‖² - ⟪φ ξ, v⟫²` is non-negative on the sphere
by Cauchy–Schwarz, and it vanishes exactly on the preimages of `± ‖v‖⁻¹ • v`; since `σ` is atomless
and carried by the sphere, this zero set is `σ`-null.  Rather than appeal to (non-)measurability of
`g` off the sphere, we glue `g` to `0` outside `Sph n`, obtaining a genuinely non-negative measurable,
bounded function `G` with `G =ᵐ[σ] g`; then `∫ g = ∫ G > 0` because the support of `G` has
`σ`-measure one.
-/

set_option linter.style.haveILetI false

namespace Work.Mostow

open MeasureTheory

noncomputable section

/-- Equality case of Cauchy–Schwarz against a unit vector: if `‖y‖ = 1` and `⟪y,v⟫² = ‖v‖²`
for `v ≠ 0`, then `y = ± ‖v‖⁻¹ • v`. -/
lemma eq_smul_or_neg_smul_of_inner_sq_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {y v : F} (hy : ‖y‖ = 1) (hv : v ≠ 0) (h : (inner ℝ y v) ^ 2 = ‖v‖ ^ 2) :
    y = ‖v‖⁻¹ • v ∨ y = -(‖v‖⁻¹ • v) := by
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set a : F := ‖v‖⁻¹ • v with ha
  have ha_norm : ‖a‖ = 1 := by
    rw [ha, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ hv0
  have hinner : inner ℝ y a = ‖v‖⁻¹ * inner ℝ y v := by
    rw [ha, real_inner_smul_right]
  have hsq : (inner ℝ y a) ^ 2 = 1 := by
    rw [hinner, mul_pow, h, ← mul_pow, inv_mul_cancel₀ hv0, one_pow]
  have ha' : a = ‖v‖⁻¹ • v := ha
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · left
    have hnorm : ‖y - a‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hy, ha_norm, h1]; ring
    have : y - a = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    rw [sub_eq_zero] at this
    rw [this, ha']
  · right
    have hnorm : ‖y + a‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, hy, ha_norm, h1]; ring
    have : y + a = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    have hy_eq : y = -a := eq_neg_of_add_eq_zero_left this
    rw [hy_eq, ha']

theorem HlinStrictMoment (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hprob : Submission.Mostow.sigma n Set.univ = 1)
    (hsupp : Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0)
    (hatom : ∀ ξ : Submission.Mostow.E n, Submission.Mostow.sigma n {ξ} = 0)
    (v : Submission.Mostow.E n) (hv : v ≠ 0) :
    0 < ∫ ξ, (‖v‖ ^ 2 - (inner ℝ (φ ξ) v) ^ 2) ∂(Submission.Mostow.sigma n) := by
  classical
  have hSph : MeasurableSet (Submission.Mostow.Sph n) := Metric.isClosed_sphere.measurableSet
  have hσSph : Submission.Mostow.sigma n (Submission.Mostow.Sph n) = 1 := by
    have h := MeasureTheory.measure_add_measure_compl (μ := Submission.Mostow.sigma n) hSph
    rw [hsupp, add_zero, hprob] at h
    exact h
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set a : Submission.Mostow.E n := ‖v‖⁻¹ • v with ha
  have ha_norm : ‖a‖ = 1 := by
    rw [ha, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ hv0
  have ha_mem : a ∈ Submission.Mostow.Sph n := by
    rw [Submission.Mostow.Sph, Metric.mem_sphere, dist_zero_right]
    exact ha_norm
  have hna_mem : -a ∈ Submission.Mostow.Sph n := by
    rw [Submission.Mostow.Sph, Metric.mem_sphere, dist_zero_right, norm_neg]
    exact ha_norm
  obtain ⟨ξ₁, hξ₁S, hξ₁⟩ := hbij.surjOn ha_mem
  obtain ⟨ξ₂, hξ₂S, hξ₂⟩ := hbij.surjOn hna_mem
  have hmapnorm : ∀ ξ ∈ Submission.Mostow.Sph n, ‖φ ξ‖ = 1 := by
    intro ξ hξS
    have hmap := hbij.mapsTo hξS
    rw [Submission.Mostow.Sph, Metric.mem_sphere, dist_zero_right] at hmap
    exact hmap
  -- the integrand vanishes only at `ξ₁`, `ξ₂`, the preimages of `± ‖v‖⁻¹ • v`
  have heqcase : ∀ ξ ∈ Submission.Mostow.Sph n,
      (inner ℝ (φ ξ) v) ^ 2 = ‖v‖ ^ 2 → ξ = ξ₁ ∨ ξ = ξ₂ := by
    intro ξ hξS h
    rcases eq_smul_or_neg_smul_of_inner_sq_eq (hmapnorm ξ hξS) hv h with h' | h'
    · left
      apply hbij.injOn hξS hξ₁S
      rw [h', ← ha]
      exact hξ₁.symm
    · right
      apply hbij.injOn hξS hξ₂S
      rw [h', ← ha]
      exact hξ₂.symm
  -- Cauchy–Schwarz on the sphere
  have hf_bound : ∀ ξ ∈ Submission.Mostow.Sph n, (inner ℝ (φ ξ) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    intro ξ hξS
    have h1 : |inner ℝ (φ ξ) v| ≤ ‖v‖ := by
      have := abs_real_inner_le_norm (φ ξ) v
      rw [hmapnorm ξ hξS, one_mul] at this
      exact this
    have h2 : |inner ℝ (φ ξ) v| ^ 2 ≤ ‖v‖ ^ 2 := by
      nlinarith [h1, abs_nonneg (inner ℝ (φ ξ) v), norm_nonneg v]
    rwa [sq_abs] at h2
  -- glue the integrand to `0` off the sphere
  set G : Submission.Mostow.E n → ℝ :=
    (Submission.Mostow.Sph n).piecewise
      (fun ξ => ‖v‖ ^ 2 - (inner ℝ (φ ξ) v) ^ 2) (fun _ => 0) with hGdef
  have hf_cont : ContinuousOn (fun ξ => ‖v‖ ^ 2 - (inner ℝ (φ ξ) v) ^ 2)
      (Submission.Mostow.Sph n) := by
    have h1 : ContinuousOn (fun ξ => inner ℝ (φ ξ) v) (Submission.Mostow.Sph n) :=
      hcont.inner continuousOn_const
    exact continuousOn_const.sub (h1.pow 2)
  have hG_meas : Measurable G := by
    rw [hGdef]
    exact hf_cont.measurable_piecewise continuousOn_const hSph
  have hG_nonneg : ∀ ξ, 0 ≤ G ξ := by
    intro ξ
    rw [hGdef]
    by_cases hξ : ξ ∈ Submission.Mostow.Sph n
    · rw [Set.piecewise_eq_of_mem _ _ _ hξ]
      linarith [hf_bound ξ hξ]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hξ]
  have hG_bound : ∀ ξ, ‖G ξ‖ ≤ ‖v‖ ^ 2 := by
    intro ξ
    rw [hGdef]
    by_cases hξ : ξ ∈ Submission.Mostow.Sph n
    · rw [Set.piecewise_eq_of_mem _ _ _ hξ, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hf_bound ξ hξ])]
      linarith [hf_bound ξ hξ, sq_nonneg (inner ℝ (φ ξ) v)]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hξ, norm_zero]
      exact sq_nonneg ‖v‖
  haveI : IsFiniteMeasure (Submission.Mostow.sigma n) :=
    ⟨by rw [hprob]; exact ENNReal.one_lt_top⟩
  have hG_int : Integrable G (Submission.Mostow.sigma n) :=
    Integrable.of_bound hG_meas.aestronglyMeasurable (‖v‖ ^ 2)
      (Filter.Eventually.of_forall hG_bound)
  -- the two preimages carry no mass
  have hpair : Submission.Mostow.sigma n ({ξ₁, ξ₂} : Set (Submission.Mostow.E n)) = 0 := by
    have hpu : ({ξ₁, ξ₂} : Set (Submission.Mostow.E n)) = {ξ₁} ∪ {ξ₂} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hpu]
    refine le_antisymm ?_ zero_le
    calc Submission.Mostow.sigma n ({ξ₁} ∪ {ξ₂})
        ≤ Submission.Mostow.sigma n {ξ₁} + Submission.Mostow.sigma n {ξ₂} :=
          measure_union_le _ _
      _ = 0 := by rw [hatom ξ₁, hatom ξ₂, add_zero]
  -- everything on the sphere except those two points lies in the support of `G`
  have hsub : Submission.Mostow.Sph n \ ({ξ₁, ξ₂} : Set (Submission.Mostow.E n)) ⊆
      Function.support G := by
    intro ξ hξ
    rw [Set.mem_sdiff] at hξ
    obtain ⟨hξS, hξpair⟩ := hξ
    rw [Function.mem_support, hGdef, Set.piecewise_eq_of_mem _ _ _ hξS]
    intro hzero
    apply hξpair
    have hinner2 : (inner ℝ (φ ξ) v) ^ 2 = ‖v‖ ^ 2 := by linarith
    rcases heqcase ξ hξS hinner2 with h | h
    · simp [h]
    · simp [h]
  have hle1 : (1 : ENNReal) ≤
      Submission.Mostow.sigma n (Submission.Mostow.Sph n \
        ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))) := by
    have hcover : Submission.Mostow.Sph n ⊆
        (Submission.Mostow.Sph n \ ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))) ∪
          ({ξ₁, ξ₂} : Set (Submission.Mostow.E n)) := by
      intro x hx
      by_cases h : x ∈ ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    calc (1 : ENNReal) = Submission.Mostow.sigma n (Submission.Mostow.Sph n) := hσSph.symm
      _ ≤ Submission.Mostow.sigma n
            ((Submission.Mostow.Sph n \ ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))) ∪
              ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))) := measure_mono hcover
      _ ≤ Submission.Mostow.sigma n
            (Submission.Mostow.Sph n \ ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))) +
          Submission.Mostow.sigma n ({ξ₁, ξ₂} : Set (Submission.Mostow.E n)) :=
          measure_union_le _ _
      _ = Submission.Mostow.sigma n
            (Submission.Mostow.Sph n \ ({ξ₁, ξ₂} : Set (Submission.Mostow.E n))) := by
          rw [hpair, add_zero]
  have hsuppG : 0 < Submission.Mostow.sigma n (Function.support G) :=
    lt_of_lt_of_le (by norm_num) (le_trans hle1 (measure_mono hsub))
  have hae : ∀ᵐ x ∂(Submission.Mostow.sigma n), x ∈ Submission.Mostow.Sph n := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hae_eq : G =ᵐ[Submission.Mostow.sigma n]
      (fun ξ => ‖v‖ ^ 2 - (inner ℝ (φ ξ) v) ^ 2) := by
    filter_upwards [hae] with x hx
    rw [hGdef, Set.piecewise_eq_of_mem _ _ _ hx]
  have hpos : 0 < ∫ ξ, G ξ ∂(Submission.Mostow.sigma n) :=
    (integral_pos_iff_support_of_nonneg hG_nonneg hG_int).mpr hsuppG
  rwa [MeasureTheory.integral_congr_ae hae_eq] at hpos

end

end Work.Mostow
