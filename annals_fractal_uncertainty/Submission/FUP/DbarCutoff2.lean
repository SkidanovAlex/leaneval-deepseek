import Submission.FUP.DbarCutoff

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The product rule for `∂̄₂` (the `S`-side of the cutoff)

This is the `(0,1) → (0,2)` analogue of `DbarCutoff.dbarAdjWeak_mul`.  If `x ∈ Dom S` with
`S x = ζ` and `χ` is a real smooth compactly supported function, then `χ x ∈ Dom S` with

  `S (χ x) = χ ζ + e`,  `e_{jk} = x_j ∂̄_k χ_ℂ - x_k ∂̄_j χ_ℂ`.

The proof tests the weak relation `DbarWeak2` against the test form `χ_ℂ Ψ`, uses the pointwise
Leibniz rule `ϑ₂(χΨ) = χ ϑ₂Ψ - e'` with `e'_j = ∑_k ∂_kχ_ℂ (Ψ_{jk} - Ψ_{kj})`, and finishes with
the antisymmetry identity `⟪Ψ, e⟫ = ⟪e', x⟫` (renaming `j ↔ k` in a double sum).
-/

namespace Submission.FUP

variable {d : ℕ}

/-- `toFormFun2` of a pointwise scalar multiple. -/
lemma toFormFun2_smul_apply (c : FormDu d → ℂ) (Ψ : FormDu d → FormSpace2 d) (z : FormDu d)
    (i : Fin d × Fin d) :
    toFormFun2 (fun w => c w • Ψ w) z i = c z * toFormFun2 Ψ z i := by
  simp only [toFormFun2_apply, WithLp.equiv_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

/-- The pointwise Leibniz rule for `ϑ₂`: multiplying a `(0,2)`-form by a complex `C¹` function. -/
lemma dbarAdjoint2_smul_apply {φ : FormDu d → ℝ} {c : FormDu d → ℂ} (hc : ContDiff ℝ 1 c)
    {Ψ : FormDu d → FormSpace2 d} (hΨ : ContDiff ℝ ∞ Ψ) (z : FormDu d) (j : Fin d) :
    dbarAdjoint2 φ (toFormFun2 (fun w => c w • Ψ w)) z j
      = c z * dbarAdjoint2 φ (toFormFun2 Ψ) z j
        - ∑ k : Fin d, partialZ k c z
            * (toFormFun2 Ψ z (j, k) - toFormFun2 Ψ z (k, j)) := by
  have hdiff : ∀ i : Fin d × Fin d, DifferentiableAt ℝ (fun w => toFormFun2 Ψ w i) z :=
    fun i => ((contDiff_toFormFun2 hΨ i).differentiable (by norm_num)) z
  have hcD : DifferentiableAt ℝ c z := hc.differentiable (by norm_num) z
  have hΔeq : ∀ k : Fin d, (fun w => toFormFun2 (fun v => c v • Ψ v) w (j, k)
        - toFormFun2 (fun v => c v • Ψ v) w (k, j))
      = fun w => c w * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) := by
    intro k; funext w; rw [toFormFun2_smul_apply, toFormFun2_smul_apply]; ring
  have hzval : ∀ k : Fin d, toFormFun2 (fun v => c v • Ψ v) z (j, k)
        - toFormFun2 (fun v => c v • Ψ v) z (k, j)
      = c z * (toFormFun2 Ψ z (j, k) - toFormFun2 Ψ z (k, j)) := by
    intro k; rw [toFormFun2_smul_apply, toFormFun2_smul_apply]; ring
  have hleib : ∀ k : Fin d,
      partialZ k (fun w => c w * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) z
        = c z * partialZ k (fun w => toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)) z
          + (toFormFun2 Ψ z (j, k) - toFormFun2 Ψ z (k, j)) * partialZ k c z :=
    fun k => partialZ_mul hcD (hdiff (j, k) |>.sub (hdiff (k, j))) k
  rw [show dbarAdjoint2 φ (toFormFun2 (fun w => c w • Ψ w)) z j
      = -∑ k : Fin d, (partialZ k (fun w => toFormFun2 (fun v => c v • Ψ v) w (j, k)
            - toFormFun2 (fun v => c v • Ψ v) w (k, j)) z
          - (toFormFun2 (fun v => c v • Ψ v) z (j, k) - toFormFun2 (fun v => c v • Ψ v) z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) from rfl]
  simp only [hΔeq, hzval, hleib]
  rw [show dbarAdjoint2 φ (toFormFun2 Ψ) z j
      = -∑ k : Fin d, (partialZ k (fun w => toFormFun2 Ψ w (j, k)
            - toFormFun2 Ψ w (k, j)) z
          - (toFormFun2 Ψ z (j, k) - toFormFun2 Ψ z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) from rfl]
  rw [mul_neg, Finset.mul_sum Finset.univ (fun k => partialZ k (fun w => toFormFun2 Ψ w (j, k)
        - toFormFun2 Ψ w (k, j)) z
      - (toFormFun2 Ψ z (j, k) - toFormFun2 Ψ z (k, j))
        * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) (c z), sub_eq_add_neg,
    ← neg_add, ← Finset.sum_add_distrib, neg_inj]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The `liftForm`-level form of the Leibniz rule: the `(0,1)`-form `ϑ₂(χΨ)`. -/
lemma liftForm_dbarAdjoint2_smul {φ : FormDu d → ℝ} {c : FormDu d → ℂ} (hc : ContDiff ℝ 1 c)
    {Ψ : FormDu d → FormSpace2 d} (hΨ : ContDiff ℝ ∞ Ψ) (w : FormDu d) :
    liftForm (dbarAdjoint2 φ (toFormFun2 (fun v => c v • Ψ v))) w
      = c w • liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) w
        - liftForm (fun w j => ∑ k : Fin d, partialZ k c w
            * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) w := by
  have hfun : dbarAdjoint2 φ (toFormFun2 (fun v => c v • Ψ v)) w
      = (fun j => c w * dbarAdjoint2 φ (toFormFun2 Ψ) w j
          - ∑ k : Fin d, partialZ k c w
              * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) :=
    funext fun j => dbarAdjoint2_smul_apply hc hΨ w j
  dsimp only [liftForm]
  rw [hfun]
  rw [show (fun j => c w * dbarAdjoint2 φ (toFormFun2 Ψ) w j
        - ∑ k : Fin d, partialZ k c w * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)))
      = c w • (dbarAdjoint2 φ (toFormFun2 Ψ) w)
        - (fun j => ∑ k : Fin d, partialZ k c w
            * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) from rfl]
  rw [WithLp.toLp_sub, WithLp.toLp_smul]

/-- The double sum of a transposed matrix. -/
lemma sum_sum_swap (N : Fin d → Fin d → ℂ) :
    (∑ j, ∑ k, N j k) = ∑ j, ∑ k, N k j := by
  rw [Finset.sum_comm]

/-- Multiplying the two arguments of an inner product by a real scalar in the complementary way. -/
lemma inner_smul_smul {ι : Type*} [Fintype ι] {c : ℂ}
    (hc : star c = c) (u v : EuclideanSpace ℂ ι) :
    inner ℂ u (c • v) = inner ℂ (c • u) v := by
  have hc' : (starRingEnd ℂ) c = c := by simpa using hc
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RCLike.inner_apply, map_mul, hc']
  ring

/-- **The antisymmetry identity** that underlies the `S`-side product rule: pairing a `(0,2)`-form
against the boundary term `e_{jk} = x_j ∂̄_k χ_ℂ - x_k ∂̄_j χ_ℂ` equals pairing `x` against
`e'_j = ∑_k ∂_kχ_ℂ (Ψ_{jk} - Ψ_{kj})`. -/
lemma inner_liftForm2_edge (χ : FormDu d → ℝ) (Ψ : FormDu d → FormSpace2 d)
    (X : FormDu d → FormSpace d) (z : FormDu d) :
    inner ℂ (Ψ z) (liftForm2 (fun w (i : Fin d × Fin d) =>
        X w i.1 * partialZbar i.2 (toC χ) w - X w i.2 * partialZbar i.1 (toC χ) w) z)
      = inner ℂ (liftForm (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
            * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) z) (X z) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [liftForm2_apply, liftForm_apply, toFormFun2_apply, WithLp.equiv_apply,
    RCLike.inner_apply, starRingEnd_apply, map_sum, map_mul, map_sub, conj_partialZ_toC]
  rw [Finset.sum_congr rfl (fun i _ => Finset.mul_sum Finset.univ
    (fun k => partialZbar k (toC χ) z * (star ((Ψ z).ofLp (i, k)) - star ((Ψ z).ofLp (k, i))))
    ((X z).ofLp i))]
  simp only [Finset.sum_sub_distrib, mul_sub, sub_mul]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  · rw [sum_sum_swap (fun i k => (X z).ofLp i * (partialZbar k (toC χ) z
        * star ((Ψ z).ofLp (k, i))))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring

/-- The `(0,1)`-form `e'_j = ∑_k ∂_kχ_ℂ (Ψ_{jk} - Ψ_{kj})` obtained from the Leibniz rule is
`L²(μ_φ)`: it is a finite sum of products of a compactly supported derivative with a compactly
supported smooth form. -/
lemma memLp_liftForm_edge {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {χ : FormDu d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsχ : HasCompactSupport χ)
    {Ψ : FormDu d → FormSpace2 d} (hΨ : ContDiff ℝ ∞ Ψ) :
    MemLp (liftForm (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
        * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)))) 2 (wtMeasure φ) := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  have hχc : ContDiff ℝ ∞ (toC χ) := contDiff_toC hχ
  have hsχc : HasCompactSupport (toC χ) := hsχ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcont : Continuous (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
      * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) := by
    rw [continuous_pi_iff]
    intro j
    refine continuous_finset_sum _ fun k _ => ?_
    exact ((contDiff_partialZ_top hχc k).continuous).mul
      (((contDiff_toFormFun2 hΨ (j, k)).continuous).sub
        ((contDiff_toFormFun2 hΨ (k, j)).continuous))
  have hcs : HasCompactSupport (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
      * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) := by
    refine hsχc.mono' ?_
    intro z hz
    by_contra hzc
    have h0 : fderiv ℝ (toC χ) z = 0 := fderiv_of_notMem_tsupport ℝ hzc
    have hp : ∀ k : Fin d, partialZ k (toC χ) z = 0 := fun k => by
      simp only [partialZ, h0, ContinuousLinearMap.zero_apply, mul_zero, sub_zero, zero_div]
    exact hz (by funext j; exact Finset.sum_eq_zero fun k _ => by rw [hp k, zero_mul])
  exact (continuous_liftForm hcont).memLp_of_hasCompactSupport (hasCompactSupport_liftForm hcs)

/-- **The product rule for `∂̄₂`.**  If `x ∈ Dom S` with `S x = ζ` and `χ` is a real smooth
compactly supported function, then `χ x ∈ Dom S` with

  `S (χ x) = χ ζ + e`,  `e_{jk} = x_j ∂̄_k χ_ℂ - x_k ∂̄_j χ_ℂ`. -/
theorem dbarWeak2_mul {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {x : H2 φ} {ζ : H3 φ}
    (hζ : DbarWeak2 φ x ζ)
    {χ : FormDu d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsχ : HasCompactSupport χ)
    (hxχ : MemLp (fun w => toC χ w • (x : FormDu d → FormSpace d) w) 2 (wtMeasure φ))
    (hζχ : MemLp (fun w => toC χ w • (ζ : FormDu d → FormSpace2 d) w) 2 (wtMeasure φ))
    (he : MemLp (liftForm2 (fun w (i : Fin d × Fin d) =>
        (x : FormDu d → FormSpace d) w i.1 * partialZbar i.2 (toC χ) w
        - (x : FormDu d → FormSpace d) w i.2 * partialZbar i.1 (toC χ) w)) 2 (wtMeasure φ)) :
    DbarWeak2 φ (hxχ.toLp (fun w => toC χ w • (x : FormDu d → FormSpace d) w))
      (hζχ.toLp (fun w => toC χ w • (ζ : FormDu d → FormSpace2 d) w)
        + he.toLp (liftForm2 (fun w (i : Fin d × Fin d) =>
            (x : FormDu d → FormSpace d) w i.1 * partialZbar i.2 (toC χ) w
            - (x : FormDu d → FormSpace d) w i.2 * partialZbar i.1 (toC χ) w))) := by
  intro Ψ h1 h2 hΨ hθ
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  have hχc : ContDiff ℝ ∞ (toC χ) := contDiff_toC hχ
  have hsχc : HasCompactSupport (toC χ) := hsχ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have h1χ : ContDiff ℝ ∞ (fun w => toC χ w • Ψ w) := hχc.smul h1
  have h2χ : HasCompactSupport (fun w => toC χ w • Ψ w) := hsχc.smul_right
  have hmemχ : MemLp (fun w => toC χ w • Ψ w) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous h1χ h2χ
  have htof : ∀ i, ContDiff ℝ 1 (fun z => toFormFun2 (fun w => toC χ w • Ψ w) z i) :=
    fun i => (contDiff_toFormFun2 h1χ i).of_le (by norm_num)
  have hcsf : HasCompactSupport (toFormFun2 (fun w => toC χ w • Ψ w)) :=
    hasCompactSupport_toFormFun2 h2χ
  have hθχ : MemLp (liftForm (dbarAdjoint2 φ (toFormFun2 (fun w => toC χ w • Ψ w))))
      2 (wtMeasure φ) := memLp_dbarAdjoint2 hφ htof hcsf
  -- the weak relation tested against `χΨ`
  have hrel := hζ (fun w => toC χ w • Ψ w) h1χ h2χ hmemχ hθχ
  -- the `(0,1)`-form produced by the Leibniz rule, and the pairing `F` against it
  have hg₂ : MemLp (liftForm (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
      * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j)))) 2 (wtMeasure φ) :=
    memLp_liftForm_edge hφ hχ hsχ h1
  have hx : MemLp ((x : FormDu d → FormSpace d)) 2 (wtMeasure φ) := Lp.memLp x
  have hstar : ∀ w : FormDu d, star (toC χ w) = toC χ w := fun w => by
    show star ((χ w : ℝ) : ℂ) = ((χ w : ℝ) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  -- ### Step 1: the three integrals
  rw [inner_add_right, inner_toLp_eq_integral hΨ hζχ, inner_toLp_eq_integral hΨ he,
    inner_toLp_eq_integral hθ hxχ]
  -- ### Step 2: the first integral is `D`
  rw [show (∫ w, inner ℂ (Ψ w) (toC χ w • (ζ : FormDu d → FormSpace2 d) w) ∂(wtMeasure φ))
      = ∫ w, inner ℂ (toC χ w • Ψ w) ((ζ : FormDu d → FormSpace2 d) w) ∂(wtMeasure φ)
      from integral_congr_ae (Eventually.of_forall fun w =>
        inner_smul_smul (hstar w) (Ψ w) ((ζ : FormDu d → FormSpace2 d) w))]
  -- ### Step 3: the second integral is `F`
  rw [show (∫ w, inner ℂ (Ψ w) (liftForm2 (fun w (i : Fin d × Fin d) =>
          (x : FormDu d → FormSpace d) w i.1 * partialZbar i.2 (toC χ) w
          - (x : FormDu d → FormSpace d) w i.2 * partialZbar i.1 (toC χ) w) w) ∂(wtMeasure φ))
      = ∫ w, inner ℂ (liftForm (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
          * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) w)
          ((x : FormDu d → FormSpace d) w) ∂(wtMeasure φ)
      from integral_congr_ae (Eventually.of_forall fun w =>
        inner_liftForm2_edge χ Ψ (x : FormDu d → FormSpace d) w)]
  -- ### Step 4: rewrite the weak relation as `D = A - F`
  rw [← Lp.toLp_coeFn ζ (Lp.memLp ζ), ← Lp.toLp_coeFn x (Lp.memLp x)] at hrel
  rw [inner_toLp_eq_integral hmemχ (Lp.memLp ζ), inner_toLp_eq_integral hθχ (Lp.memLp x)] at hrel
  rw [show (∫ w, inner ℂ (liftForm (dbarAdjoint2 φ (toFormFun2 (fun w => toC χ w • Ψ w))) w)
          ((x : FormDu d → FormSpace d) w) ∂(wtMeasure φ))
      = (∫ w, inner ℂ (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) w)
            (toC χ w • (x : FormDu d → FormSpace d) w) ∂(wtMeasure φ))
        - ∫ w, inner ℂ (liftForm (fun w j => ∑ k : Fin d, partialZ k (toC χ) w
            * (toFormFun2 Ψ w (j, k) - toFormFun2 Ψ w (k, j))) w)
            ((x : FormDu d → FormSpace d) w) ∂(wtMeasure φ)
      from by
        rw [← integral_sub
          (integrable_inner_toLp hθ hxχ)
          (integrable_inner_toLp hg₂ hx)]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [liftForm_dbarAdjoint2_smul (φ := φ) (hχc.of_le (by norm_num)) h1 w,
          inner_sub_left, inner_smul_smul (hstar w)]] at hrel
  -- ### Step 5: assemble
  rw [hrel]
  ring

end Submission.FUP
