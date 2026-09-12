import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarStruct

/-!
# ModelStarExterior -- the exterior map `modelF` up to the boundary

For the model map `F = modelF z₀ r` (`z₀ k` distinct unit points, `r k > 0`,
`Σ r k = 1`) this module develops the boundary/exterior structure of `F`
and of its boundary image `M := F '' {‖ζ‖ = 1}`:

* `modelFactor_continuousWithinAt` / `modelFactor_continuousOn` /
  **`modelF_continuousOn_closedExterior`**: `F` is continuous on the closed
  exterior `{1 ≤ ‖z‖}`, INCLUDING the junctions `z₀ k` (where the factor
  tends to `0` through `‖1 - z₀ k·z⁻¹‖ = ‖z-z₀ k‖/‖z‖ → 0`);
* `circle_eq_range_exp`, `isPreconnected_unitCircle`, `isConnected_circle`:
  the unit circle is the image of `ℝ` under `θ ↦ exp(θ·I)`;
* `isCompact_modelStarImage`, `isPreconnected_modelStarImage`: `M` is a
  compact continuum (in particular it has NO isolated point, `M` being a
  preconnected set with more than one point);
* `modelStarImage_two_le` : `M` contains at least two points.

The remaining ("counting") half of "`F` is the exterior map of `M`" —
`F '' {1 < ‖z‖} ∩ M = ∅`, equivalent to (P3) of
`Submission/Work/STATUS_dimitrov.md` §120 — is NOT proved here; it needs the
exact number of exterior preimages (`N(w) = 1` for `w ∉ M`), i.e. the
Rouché/argument-principle chapter missing from Mathlib.
-/

noncomputable section
open scoped Real BigOperators Topology
open Filter Set

namespace Submission.ModelStarExterior

open Submission.ModelStarMap
open Submission.ModelStarStruct

/-! ## §1  Continuity of the model map on the closed exterior -/

/-- The factor base lies in the closed right half plane on `{1 ≤ ‖z‖}`. -/
lemma factor_re_nonneg {a z : ℂ} (ha : ‖a‖ = 1) (hz : 1 ≤ ‖z‖) :
    0 ≤ (1 - a * z⁻¹).re := by
  have hnorm : ‖a * z⁻¹‖ = 1 / ‖z‖ := by
    rw [norm_mul, norm_inv, ha, one_mul, one_div]
  have hre : (1 - a * z⁻¹).re = 1 - (a * z⁻¹).re := by simp
  rw [hre]
  have h1 : (a * z⁻¹).re ≤ 1 / ‖z‖ := by
    calc (a * z⁻¹).re ≤ ‖a * z⁻¹‖ := Complex.re_le_norm _
      _ = 1 / ‖z‖ := hnorm
  have h2 : 1 / ‖z‖ ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hz)).mpr hz
  linarith

/-- At a junction `a` the model factor tends to `0`. -/
lemma modelFactor_tendsto_junction {a : ℂ} {t : ℝ} (ht : 0 < t) (ha : ‖a‖ = 1) :
    Tendsto (fun z : ℂ => modelFactor a t z) (𝓝 a) (𝓝 0) := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun z : ℂ => ‖modelFactor a t z‖) = fun z => ‖1 - a * z⁻¹‖ ^ t := by
    funext z; exact norm_modelFactor
  rw [h1]
  have h2 : (fun z : ℂ => ‖1 - a * z⁻¹‖ ^ t) =ᶠ[𝓝 a] fun z => (‖z - a‖ / ‖z‖) ^ t := by
    filter_upwards [isOpen_ne.mem_nhds ha0] with z hz
    rw [norm_factor_div hz]
  refine Tendsto.congr' h2.symm ?_
  have hnorm : Tendsto (fun z : ℂ => ‖z - a‖ / ‖z‖) (𝓝 a) (𝓝 0) := by
    have ha0' : ‖a‖ ≠ 0 := by rw [ha]; norm_num
    have hnum : Tendsto (fun z : ℂ => ‖z - a‖) (𝓝 a) (𝓝 ‖a - a‖) :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).tendsto a
    have h := hnum.div continuous_norm.continuousAt ha0'
    rwa [sub_self, norm_zero, zero_div] at h
  have h3 := (Real.continuousAt_rpow_const 0 t (Or.inr ht.le)).tendsto.comp hnorm
  simpa [Function.comp_def, Real.zero_rpow (ne_of_gt ht)] using h3

/-- Continuity of the model factor on the closed exterior. -/
lemma modelFactor_continuousWithinAt {a : ℂ} {t : ℝ} (ht : 0 < t) (ha : ‖a‖ = 1)
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ContinuousWithinAt (fun w : ℂ => modelFactor a t w) {z : ℂ | 1 ≤ ‖z‖} z := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  rcases eq_or_ne z a with hza | haz
  · rw [hza] at hz ⊢
    clear hza z
    have hfa : modelFactor a t a = 0 := by
      have h1 : 1 - a * a⁻¹ = 0 := by rw [mul_inv_cancel₀ ha0, sub_self]
      simp only [modelFactor, h1]
      exact Complex.zero_cpow (by exact_mod_cast ne_of_gt ht)
    have h := modelFactor_tendsto_junction ht ha
    have h2 : ContinuousAt (fun z : ℂ => modelFactor a t z) a := by
      rw [ContinuousAt, hfa]; exact h
    exact h2.continuousWithinAt
  · have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    have hsp : 1 - a * z⁻¹ ∈ Complex.slitPlane :=
      one_sub_mul_inv_mem_slitPlane ha hz haz
    have hinner : ContinuousAt (fun w : ℂ => 1 - a * w⁻¹) z := by
      refine ContinuousAt.sub continuousAt_const ?_
      exact ContinuousAt.mul continuousAt_const ((continuousAt_id).inv₀ hz0)
    have hlog : ContinuousAt (fun w : ℂ => Complex.log (1 - a * w⁻¹)) z := by
      have := ContinuousAt.comp (f := fun w : ℂ => 1 - a * w⁻¹) (g := Complex.log) (x := z)
        ((Complex.differentiableAt_log hsp).continuousAt) hinner
      simpa [Function.comp_def] using this
    have hexp : ContinuousAt
        (fun w : ℂ => Complex.exp ((t : ℂ) * Complex.log (1 - a * w⁻¹))) z :=
      ContinuousAt.cexp (continuousAt_const.mul hlog)
    refine hexp.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds haz),
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz0)]
        with w _ hwa hw0
      exact modelFactor_eq_exp hw0 hwa
    · exact modelFactor_eq_exp hz0 haz

lemma modelFactor_continuousOn {a : ℂ} {t : ℝ} (ht : 0 < t) (ha : ‖a‖ = 1) :
    ContinuousOn (fun z : ℂ => modelFactor a t z) {z : ℂ | 1 ≤ ‖z‖} :=
  fun _ hz => modelFactor_continuousWithinAt ht ha hz

/-- **Continuity of the model map on the closed exterior.** -/
theorem modelF_continuousOn_closedExterior {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    ContinuousOn (fun z : ℂ => modelF z₀ r z) {z : ℂ | 1 ≤ ‖z‖} := by
  have hprod : ContinuousOn (fun z : ℂ => ∏ k : Fin n, modelFactor (z₀ k) (2 * r k) z)
      {z : ℂ | 1 ≤ ‖z‖} := by
    refine continuousOn_finset_prod _ (fun k _ => ?_)
    exact modelFactor_continuousOn (by linarith [hr k]) (hunit k)
  exact (continuousOn_id.mul hprod).congr (fun z _ => rfl)

/-! ## §2  The unit circle and the model-star image -/

/-- The unit circle. -/
def unitCircle : Set ℂ := Metric.sphere (0 : ℂ) 1

lemma mem_circle {z : ℂ} : z ∈ unitCircle ↔ ‖z‖ = 1 := by
  rw [unitCircle, Metric.mem_sphere, dist_eq_norm, sub_zero]

/-- The unit unitCircle is the range of `θ ↦ exp (θ·I)`. -/
lemma circle_eq_range_exp : unitCircle = Set.range (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by
  ext ζ
  rw [mem_circle]
  constructor
  · intro hζ
    refine ⟨ζ.arg, ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I ζ
    have h1 : (↑‖ζ‖ : ℂ) = 1 := by rw [hζ]; norm_num
    rw [h1, one_mul] at h
    exact h
  · rintro ⟨θ, rfl⟩
    rw [Complex.norm_exp]
    simp [Complex.ofReal_im]

lemma isPreconnected_unitCircle : IsPreconnected unitCircle := by
  rw [circle_eq_range_exp]
  exact isPreconnected_range
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))

/-- The model-star image `M = F '' unitCircle`. -/
def modelStarImage {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) : Set ℂ :=
  modelF z₀ r '' unitCircle

lemma isCompact_modelStarImage {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    IsCompact (modelStarImage z₀ r) := by
  refine IsCompact.image_of_continuousOn (isCompact_sphere (0 : ℂ) 1) ?_
  exact (modelF_continuousOn_closedExterior z₀ r hunit hr).mono (fun z hz => by
    rw [mem_circle] at hz
    rw [Set.mem_setOf_eq, hz])

lemma isPreconnected_modelStarImage {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    IsPreconnected (modelStarImage z₀ r) := by
  have hcont : ContinuousOn (fun z : ℂ => modelF z₀ r z) unitCircle :=
    (modelF_continuousOn_closedExterior z₀ r hunit hr).mono
      (fun z hz => by rw [mem_circle] at hz; rw [Set.mem_setOf_eq, hz])
  unfold modelStarImage
  exact @IsPreconnected.image ℂ ℂ _ _ unitCircle isPreconnected_unitCircle
    (fun z : ℂ => modelF z₀ r z) hcont

/-- The points `exp (2πi/(m+1))` of the unit circle. -/
def circleSeq (m : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((m : ℂ) + 1))

lemma circleSeq_mem (m : ℕ) : circleSeq m ∈ unitCircle := by
  rw [mem_circle, circleSeq, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I / ((m : ℂ) + 1)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.normSq, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  rw [hre, Real.exp_zero]

lemma circleSeq_injective : Function.Injective circleSeq := by
  intro m m' hmm
  have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hmm' : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((m : ℂ) + 1)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((m' : ℂ) + 1)) := hmm
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((m : ℂ) + 1) -
      2 * (Real.pi : ℂ) * Complex.I / ((m' : ℂ) + 1)) = 1 := by
    rw [Complex.exp_sub, hmm', div_self (Complex.exp_ne_zero _)]
  obtain ⟨N, hN⟩ := Complex.exp_eq_one_iff.mp h1
  have hfac : 2 * (Real.pi : ℂ) * Complex.I / ((m : ℂ) + 1) -
      2 * (Real.pi : ℂ) * Complex.I / ((m' : ℂ) + 1) =
      (1 / ((m : ℂ) + 1) - 1 / ((m' : ℂ) + 1)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
  rw [hfac] at hN
  have hNc : 1 / ((m : ℂ) + 1) - 1 / ((m' : ℂ) + 1) = (N : ℂ) :=
    mul_right_cancel₀ hC hN
  have hNr : 1 / ((m : ℝ) + 1) - 1 / ((m' : ℝ) + 1) = (N : ℝ) := by
    have h := congrArg Complex.re hNc
    have hc1 : (1 / ((m : ℂ) + 1)) = ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
    have hc2 : (1 / ((m' : ℂ) + 1)) = ((1 / ((m' : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [hc1, hc2, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at h
    have hNre : ((N : ℂ)).re = (N : ℝ) := by simp
    rw [hNre] at h
    exact h
  have hN0 : N = 0 := by
    have habs : |(N : ℝ)| < 1 := by
      rw [abs_lt]
      have h1 : 0 < 1 / ((m : ℝ) + 1) := by positivity
      have h2 : 0 < 1 / ((m' : ℝ) + 1) := by positivity
      have h3 : 1 / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; norm_num
      have h4 : 1 / ((m' : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; norm_num
      constructor <;> linarith
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast habs : |N| < 1)
  have heq : 1 / ((m : ℝ) + 1) = 1 / ((m' : ℝ) + 1) := by
    have : (1 / ((m : ℝ) + 1) - 1 / ((m' : ℝ) + 1)) = 0 := by rw [hNr, hN0]; norm_num
    linarith
  have hm : ((m : ℝ) + 1) = ((m' : ℝ) + 1) := by
    rw [one_div, one_div, inv_inj] at heq
    exact heq
  have : ((m + 1 : ℕ) : ℝ) = ((m' + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact Nat.succ.inj (Nat.cast_injective this)

/-- The unit circle is infinite. -/
lemma infinite_unitCircle : Set.Infinite unitCircle :=
  (Set.infinite_range_of_injective circleSeq_injective).mono (by
    rintro _ ⟨m, rfl⟩
    exact circleSeq_mem m)

/-- Some point of the unit circle is not a junction. -/
lemma exists_unitCircle_ne {n : ℕ} (z₀ : Fin n → ℂ) :
    ∃ ζ ∈ unitCircle, ∀ k, ζ ≠ z₀ k := by
  obtain ⟨ζ, hζ, hne⟩ :=
    infinite_unitCircle.exists_notMem_finset (Finset.image z₀ Finset.univ)
  exact ⟨ζ, hζ, fun k hk => hne (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩)⟩

/-! ## §3  The model star is a nondegenerate continuum -/

/-- `modelF` vanishes at the junctions. -/
lemma modelF_junction_eq_zero {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (k : Fin n) :
    modelF z₀ r (z₀ k) = 0 := by
  have hzk : z₀ k ≠ 0 := norm_ne_zero_iff.mp (by rw [hunit k]; norm_num)
  have hfac : modelFactor (z₀ k) (2 * r k) (z₀ k) = 0 := by
    unfold modelFactor
    rw [show 1 - z₀ k * (z₀ k)⁻¹ = 0 by rw [mul_inv_cancel₀ hzk, sub_self]]
    exact Complex.zero_cpow (by
      have : (0 : ℝ) < 2 * r k := by linarith [hr k]
      exact_mod_cast (ne_of_gt this) : ((2 * r k : ℝ) : ℂ) ≠ 0)
  unfold modelF modelProduct
  rw [Finset.prod_eq_zero (Finset.mem_univ k) hfac, mul_zero]

/-- `modelF` does not vanish at a point of the unit circle that is not a
junction. -/
lemma modelF_unitCircle_ne_zero {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    {ζ : ℂ} (hζ : ζ ∈ unitCircle) (hne : ∀ k, ζ ≠ z₀ k) :
    modelF z₀ r ζ ≠ 0 := by
  rw [mem_circle] at hζ
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; norm_num)
  have hfac : ∀ k : Fin n, modelFactor (z₀ k) (2 * r k) ζ ≠ 0 := by
    intro k
    have h1 : 1 - z₀ k * ζ⁻¹ ≠ 0 := by
      intro h
      apply hne k
      have := (sub_eq_zero.mp h).symm
      calc ζ = ζ * 1 := by ring
        _ = ζ * (z₀ k * ζ⁻¹) := by rw [this]
        _ = z₀ k := by field_simp
    unfold modelFactor
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl h1)
  unfold modelF modelProduct
  exact mul_ne_zero hζ0 (Finset.prod_ne_zero_iff.mpr (fun k _ => hfac k))

/-- The model star has at least two distinct points. -/
lemma modelStarImage_two {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hn : 0 < n) :
    ∃ a ∈ modelStarImage z₀ r, ∃ b ∈ modelStarImage z₀ r, a ≠ b := by
  obtain ⟨ζ, hζ, hζne⟩ := exists_unitCircle_ne z₀
  refine ⟨0, ⟨z₀ ⟨0, hn⟩, by rw [mem_circle, hunit], modelF_junction_eq_zero z₀ r hunit hr _⟩,
    modelF z₀ r ζ, ⟨ζ, hζ, rfl⟩, ?_⟩
  intro h
  exact modelF_unitCircle_ne_zero z₀ r hζ hζne h.symm

end Submission.ModelStarExterior
