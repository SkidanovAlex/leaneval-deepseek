import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped FourierTransform Topology SchwartzMap

noncomputable section

/-! ## Auxiliary lemmas for the sublattice Shannon reproduction theorem -/

/-- Affine substitution for the Lebesgue integral on `ℝ`. -/
lemma shannon_integral_comp_sub_mul_add (g : ℝ → ℂ) {a c : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, g (c - a * t)) = ((a : ℂ))⁻¹ * (∫ u : ℝ, g u) := by
  have h1 : (∫ t : ℝ, g (c - a * t)) =
      ∫ t : ℝ, (fun u : ℝ => g (u + c)) ((-a) * t) := by
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    ring
  rw [h1, Measure.integral_comp_mul_left (fun u : ℝ => g (u + c)) (-a),
    integral_add_right_eq_self g c]
  have h2 : ((-a) : ℝ)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
  rw [abs_of_neg h2, inv_neg, neg_neg]
  rw [Complex.real_smul, Complex.ofReal_inv]

/-- The Fourier character is multiplicative. -/
lemma shannon_fourierChar_mul (x y : ℝ) : (𝐞 x : ℂ) * (𝐞 y : ℂ) = (𝐞 (x + y) : ℂ) := by
  simp only [Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier character has modulus one. -/
lemma shannon_norm_fourierChar (x : ℝ) : ‖(𝐞 x : ℂ)‖ = 1 := Circle.norm_coe _

/-- `(2:ℝ)^{-2} = 1/4`. -/
lemma shannon_two_rpow_neg_two : (2:ℝ) ^ (-2:ℝ) = 1/4 := by
  have h : (2:ℝ) ^ (2:ℝ) = 4 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num), h]
  norm_num

/-- `1 + |t|` is controlled by `1 + |a t + c|` for `a > 0`. -/
lemma shannon_one_add_le_affine {a c : ℝ} (ha : 0 < a) (t : ℝ) :
    1 + |t| ≤ (1 + |c| / a + a⁻¹) * (1 + |a * t + c|) := by
  have ha' : (0:ℝ) < a := ha
  have hcinv : (0:ℝ) ≤ |c| / a := by positivity
  have hainv : (0:ℝ) ≤ a⁻¹ := by positivity
  have hL2 : a⁻¹ ≤ 1 + |c| / a + a⁻¹ := by linarith
  have h1 : |t| = |a * t| / a := by
    rw [abs_mul, abs_of_pos ha', mul_div_cancel_left₀ _ ha'.ne']
  have h2 : |a * t| ≤ |a * t + c| + |c| := by
    have h := abs_add_le (a * t + c) (-c)
    rw [abs_neg] at h
    have he : a * t + c + -c = a * t := by ring
    rwa [he] at h
  have h3 : |t| ≤ (|a * t + c| + |c|) / a := by
    rw [h1, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h2 hainv
  have h4 : (|a * t + c| + |c|) / a = |c| / a + |a * t + c| / a := by
    rw [add_div, add_comm]
  have h5 : |a * t + c| / a ≤ (1 + |c| / a + a⁻¹) * |a * t + c| := by
    rw [div_eq_mul_inv, mul_comm (|a * t + c|) a⁻¹]
    exact mul_le_mul_of_nonneg_right hL2 (abs_nonneg _)
  have h6 : 1 + |c| / a + |a * t + c| / a ≤
      (1 + |c| / a + a⁻¹) * (1 + |a * t + c|) := by
    nlinarith [h5, hcinv, hainv, abs_nonneg (a * t + c),
      mul_nonneg hcinv (abs_nonneg (a * t + c))]
  linarith [h3, h4, h6]

/-- A linear comparison `1+|X| ≤ L (1+|Y|)` implies `(1+|Y|)^{-b} ≤ L^b (1+|X|)^{-b}`. -/
lemma shannon_rpow_affine_bound {b L : ℝ} (hb : 0 < b) (hL : 0 < L) {X Y : ℝ}
    (h : 1 + |X| ≤ L * (1 + |Y|)) :
    (1 + |Y|) ^ (-b) ≤ L ^ b * (1 + |X|) ^ (-b) := by
  have h1 : L⁻¹ * (1 + |X|) ≤ 1 + |Y| := by
    rw [inv_mul_le_iff₀ hL]
    linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (x := L⁻¹ * (1 + |X|)) (y := 1 + |Y|)
    (by positivity) h1 (by linarith : -b ≤ 0)
  rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (le_of_lt hL),
    Real.rpow_neg (le_of_lt hL), inv_inv] at h2
  exact h2

/-- `(1+|x|)^{-b}` dominates `|x|^{-b}` at infinity. -/
lemma shannon_one_add_rpow_le {b : ℝ} (hb : 0 < b) {x : ℝ} (hx : 1 ≤ |x|) :
    (1 + |x|) ^ (-b) ≤ |x| ^ (-b) := by
  refine Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < |x| by linarith) ?_ (by linarith : -b ≤ 0)
  linarith [abs_nonneg x]

/-- A pointwise bound by `C (1+|x|)^{-b}` gives `|·|^{-b}` decay at infinity. -/
lemma shannon_isBigO_of_one_add_bound (f : ℝ → ℂ) {b C : ℝ} (hb : 0 < b)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-b)) :
    f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound (max C 0) ?_
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup]
  constructor
  · rw [Filter.eventually_atBot]
    refine ⟨-1, fun x hx => ?_⟩
    have hxabs : 1 ≤ |x| := by
      rw [abs_of_nonpos (by linarith : x ≤ 0)]
      linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    have hm : C * (1 + |x|) ^ (-b) ≤ max C 0 * (1 + |x|) ^ (-b) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by positivity) _)
    exact (hf x).trans (hm.trans (mul_le_mul_of_nonneg_left (shannon_one_add_rpow_le hb hxabs)
      (le_max_right C 0)))
  · rw [Filter.eventually_atTop]
    refine ⟨1, fun x hx => ?_⟩
    have hxabs : 1 ≤ |x| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ x)]
      linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    have hm : C * (1 + |x|) ^ (-b) ≤ max C 0 * (1 + |x|) ^ (-b) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by positivity) _)
    exact (hf x).trans (hm.trans (mul_le_mul_of_nonneg_left (shannon_one_add_rpow_le hb hxabs)
      (le_max_right C 0)))

/-- Summability over `ℤ` of `(1+|n|)^{-b}` for `b > 1`. -/
lemma shannon_one_add_rpow_int_summable {b : ℝ} (hb : 1 < b) :
    Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ (-b)) := by
  have h1 : Summable (fun j : ℤ => if j = 0 then (0:ℝ) else (1 + |(j:ℝ)|) ^ (-b)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (Real.summable_abs_int_rpow hb)
    · by_cases h : j = 0
      · simp [h]
      · simp only [h, if_false]
        exact Real.rpow_nonneg (by positivity) _
    · by_cases h : j = 0
      · simp [h, Real.rpow_nonneg]
      · simp only [h, if_false]
        refine Real.rpow_le_rpow_of_nonpos (x := |(j:ℝ)|) (y := 1 + |(j:ℝ)|) ?_ ?_ ?_
        · exact abs_pos.mpr (by exact_mod_cast h)
        · linarith [abs_nonneg (j:ℝ)]
        · linarith
  have h2 : Summable (fun j : ℤ => if j = 0 then (1 + |(j:ℝ)|) ^ (-b) else (0:ℝ)) :=
    summable_of_ne_finset_zero (s := {0}) (fun j hj => by
      simp only [Finset.mem_singleton] at hj
      simp [hj])
  have h3 := h1.add h2
  refine h3.congr (fun j => ?_)
  by_cases h : j = 0 <;> simp [h]

/-- Pointwise Schwartz decay in the form `‖f x‖ ≤ C (1+|x|)^{-2}`. -/
lemma shannon_schwartz_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-2 : ℝ) := by
  obtain ⟨C₀, hC₀, h0⟩ := f.decay 0 0
  obtain ⟨C₂, hC₂, h2⟩ := f.decay 2 0
  have h0' : ∀ x : ℝ, ‖f x‖ ≤ C₀ := by
    intro x
    have h := h0 x
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    exact h
  have h2' : ∀ x : ℝ, ‖f x‖ * |x| ^ (2:ℝ) ≤ C₂ := by
    intro x
    have h := h2 x
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_zero, ← Real.rpow_natCast] at h
    rwa [mul_comm] at h
  refine ⟨max (4 * C₀) (4 * C₂), by positivity, fun x => ?_⟩
  rcases le_or_gt (1:ℝ) |x| with hx | hx
  · have hlt : (0:ℝ) < |x| := by linarith
    have h4 : ‖f x‖ ≤ C₂ * |x| ^ (-2:ℝ) := by
      have h5 : ‖f x‖ ≤ C₂ / |x| ^ (2:ℝ) := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hlt 2)]
        exact h2' x
      rw [div_eq_mul_inv, ← Real.rpow_neg (abs_nonneg x) (2:ℝ)] at h5
      exact h5
    have h6 : |x| ^ (-2:ℝ) ≤ 4 * (1 + |x|) ^ (-2:ℝ) := by
      have h7 : (2 * |x|) ^ (-2:ℝ) ≤ (1 + |x|) ^ (-2:ℝ) := by
        refine Real.rpow_le_rpow_of_nonpos (x := 1 + |x|) (y := 2 * |x|) (z := -2) ?_ ?_ ?_
        · positivity
        · linarith
        · norm_num
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg x),
        shannon_two_rpow_neg_two] at h7
      linarith
    calc ‖f x‖ ≤ C₂ * |x| ^ (-2:ℝ) := h4
      _ ≤ C₂ * (4 * (1 + |x|) ^ (-2:ℝ)) := mul_le_mul_of_nonneg_left h6 hC₂.le
      _ = (4 * C₂) * (1 + |x|) ^ (-2:ℝ) := by ring
      _ ≤ max (4 * C₀) (4 * C₂) * (1 + |x|) ^ (-2:ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
  · have h6 : (1:ℝ) ≤ 4 * (1 + |x|) ^ (-2:ℝ) := by
      have h7 : (2:ℝ) ^ (-2:ℝ) ≤ (1 + |x|) ^ (-2:ℝ) := by
        refine Real.rpow_le_rpow_of_nonpos (x := 1 + |x|) (y := 2) (z := -2) ?_ ?_ ?_
        · positivity
        · linarith [abs_nonneg x, hx.le]
        · norm_num
      rw [shannon_two_rpow_neg_two] at h7
      linarith
    have h8 : C₀ ≤ (4 * C₀) * (1 + |x|) ^ (-2:ℝ) := by
      have h9 : (4 * C₀) * (1 + |x|) ^ (-2:ℝ) = C₀ * (4 * (1 + |x|) ^ (-2:ℝ)) := by ring
      rw [h9]
      exact le_mul_of_one_le_right hC₀.le h6
    calc ‖f x‖ ≤ C₀ := h0' x
      _ ≤ (4 * C₀) * (1 + |x|) ^ (-2:ℝ) := h8
      _ ≤ max (4 * C₀) (4 * C₂) * (1 + |x|) ^ (-2:ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)

/-- Existence of a smooth compactly supported cut-off which is `1` on `[-β, β]` and
supported in an interval still contained in `(-1/(2q), 1/(2q))`. -/
lemma shannon_exists_bump (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : 0 < q)
    (hβq : β * (q : ℝ) < 1 / 2) :
    ∃ dc : ℝ, β < dc ∧ dc < 1 / (2 * (q : ℝ)) ∧
      ∃ χ : 𝓢(ℝ, ℂ), (∀ ξ ∈ Set.Icc (-β) β, (χ : ℝ → ℂ) ξ = 1) ∧
        (∀ ξ : ℝ, dc ≤ |ξ| → (χ : ℝ → ℂ) ξ = 0) := by
  have hq' : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hβ1 : β < 1 / (2 * (q:ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hβq]
  refine ⟨(β + 1 / (2 * (q:ℝ))) / 2, by linarith, by linarith, ?_⟩
  let bump : ContDiffBump (0:ℝ) := ⟨β, (β + 1/(2*(q:ℝ)))/2, hβ, by linarith⟩
  have hcs : HasCompactSupport (fun x : ℝ => (bump x : ℂ)) := by
    have h := HasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) bump.hasCompactSupport
      (by norm_num)
    convert h using 1
    ext x
    rfl
  refine ⟨hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff), ?_, ?_⟩
  · intro ξ hξ
    have h1 := bump.one_of_mem_closedBall (x := ξ) ?_
    · change ((bump : ℝ → ℝ) ξ : ℂ) = 1
      exact_mod_cast h1
    · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      exact ⟨hξ.1, hξ.2⟩
  · intro ξ hξ
    have h1 := bump.zero_of_le_dist (x := ξ) ?_
    · change ((bump : ℝ → ℝ) ξ : ℂ) = 0
      exact_mod_cast h1
    · rw [Real.dist_eq, sub_zero]
      exact hξ

/-- Fourier inversion for an integrable continuous function whose Fourier transform is
supported in the band `[-β,β]`. -/
lemma shannon_bandlimited_inversion (β : ℝ) (γ : ℝ → ℂ) (hint : Integrable γ)
    (hcont : Continuous γ)
    (hsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → 𝓕 γ ξ = 0) :
    Integrable (𝓕 γ) ∧ ∀ y : ℝ, γ y = ∫ ξ : ℝ, (𝐞 (ξ * y) : ℂ) * 𝓕 γ ξ := by
  have hcontF : Continuous (𝓕 γ) := by
    change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) γ)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hint
  have hcs : HasCompactSupport (𝓕 γ) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-β) β) isCompact_Icc
      (fun y hy => ?_)
    by_contra h
    exact hy (hsupp y h)
  have hFint : Integrable (𝓕 γ) := hcontF.integrable_of_hasCompactSupport hcs
  refine ⟨hFint, fun y => ?_⟩
  have h1 : 𝓕⁻ (𝓕 γ) y = γ y := Integrable.fourierInv_fourier_eq hint hFint hcont.continuousAt
  rw [← h1, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [Circle.smul_def, smul_eq_mul, Real.inner_apply]

/-- **Poisson summation along an arithmetic progression** (the "decimation" identity):
sampling a decaying continuous function `k` (with decaying Fourier transform) on
the arithmetic progression `c - a ℤ` and modulating by a character gives the Poisson
sum of the modulated Fourier transform. -/
lemma shannon_decimation_poisson (k : ℝ → ℂ) (hk : Continuous k) {b C : ℝ} (hb : 1 < b)
    (hC : 0 ≤ C)
    (hkd : ∀ x : ℝ, ‖k x‖ ≤ C * (1 + |x|) ^ (-b))
    (hFd : ∀ y : ℝ, ‖𝓕 k y‖ ≤ C * (1 + |y|) ^ (-b))
    {a : ℝ} (ha : 0 < a) (c ξ : ℝ) :
    ∑' m : ℤ, k (c - a * (m : ℝ)) * (𝐞 (-(ξ * (c - a * (m : ℝ)))) : ℂ)
      = ((a : ℂ))⁻¹ * ∑' j : ℤ, 𝓕 k (ξ - (j : ℝ) / a) * (𝐞 (-((j : ℝ) / a * c)) : ℂ) := by
  have hb0 : (0:ℝ) < b := zero_lt_one.trans hb
  set ψ : ℝ → ℂ := fun t => k (c - a * t) * (𝐞 (-(ξ * (c - a * t))) : ℂ) with hψdef
  have hL1pos : (0:ℝ) < 1 + |c| / a + a⁻¹ := by positivity
  have hψcont : Continuous ψ := by
    rw [hψdef]
    refine (hk.comp (by fun_prop : Continuous fun t : ℝ => c - a * t)).mul ?_
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hψd : ψ =O[cocompact ℝ] (fun t : ℝ => |t| ^ (-b)) := by
    refine shannon_isBigO_of_one_add_bound (C := C * (1 + |c| / a + a⁻¹) ^ b) ψ hb0
      (fun t => ?_)
    rw [hψdef, norm_mul, shannon_norm_fourierChar, mul_one]
    have hle : 1 + |t| ≤ (1 + |c| / a + a⁻¹) * (1 + |c - a * t|) := by
      have h := shannon_one_add_le_affine (a := a) (c := c) ha (-t)
      rw [abs_neg, show a * (-t) + c = c - a * t from by ring] at h
      exact h
    have h1 := shannon_rpow_affine_bound hb0 hL1pos hle
    calc ‖k (c - a * t)‖ ≤ C * (1 + |c - a * t|) ^ (-b) := hkd _
      _ ≤ C * ((1 + |c| / a + a⁻¹) ^ b * (1 + |t|) ^ (-b)) :=
            mul_le_mul_of_nonneg_left h1 hC
      _ = (C * (1 + |c| / a + a⁻¹) ^ b) * (1 + |t|) ^ (-b) := by ring
  have hform : ∀ y : ℝ, 𝓕 ψ y = ((a : ℂ))⁻¹ * (𝐞 (-(y / a * c)) : ℂ) * 𝓕 k (ξ - y / a) := by
    intro y
    set G : ℝ → ℂ := fun u => (𝐞 (-(y / a * c)) : ℂ) *
      (k u * (𝐞 (-((ξ - y / a) * u)) : ℂ)) with hG
    have hsub := shannon_integral_comp_sub_mul_add (c := c) G ha
    have h1 : (∫ v : ℝ, 𝐞 (-inner ℝ v y) • ψ v) = ∫ t : ℝ, G (c - a * t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hψdef, hG, Circle.smul_def, smul_eq_mul, Real.inner_apply]
      have harg : -(t * y) + -(ξ * (c - a * t)) =
          -(y / a * c) + -((ξ - y / a) * (c - a * t)) := by
        field_simp
        ring
      calc (𝐞 (-(t * y)) : ℂ) * (k (c - a * t) * (𝐞 (-(ξ * (c - a * t))) : ℂ))
          = ((𝐞 (-(t * y)) : ℂ) * (𝐞 (-(ξ * (c - a * t))) : ℂ)) * k (c - a * t) := by
            ring
        _ = (𝐞 (-(t * y) + -(ξ * (c - a * t))) : ℂ) * k (c - a * t) := by
              rw [shannon_fourierChar_mul]
        _ = (𝐞 (-(y / a * c) + -((ξ - y / a) * (c - a * t))) : ℂ) * k (c - a * t) := by
              rw [harg]
        _ = ((𝐞 (-(y / a * c)) : ℂ) *
              (𝐞 (-((ξ - y / a) * (c - a * t))) : ℂ)) * k (c - a * t) := by
              rw [shannon_fourierChar_mul]
        _ = (𝐞 (-(y / a * c)) : ℂ) *
              (k (c - a * t) * (𝐞 (-((ξ - y / a) * (c - a * t))) : ℂ)) := by ring
    have h2 : (∫ u : ℝ, G u) = (𝐞 (-(y / a * c)) : ℂ) * 𝓕 k (ξ - y / a) := by
      rw [hG, integral_const_mul]
      congr 1
      rw [Real.fourier_eq]
      simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      filter_upwards with u
      have harg : -((ξ - y / a) * u) = -(u * (ξ - y / a)) := by ring
      rw [harg]
      ring
    rw [Real.fourier_eq, h1, hsub, h2]
    ring
  have hL2pos : (0:ℝ) < 1 + a * |ξ| + a := by positivity
  have hψsum : Summable (fun j : ℤ => 𝓕 ψ (j : ℝ)) := by
    refine summable_of_isBigO (shannon_one_add_rpow_int_summable hb)
      (Asymptotics.IsBigO.of_bound (‖((a : ℂ))⁻¹‖ * (C * (1 + a * |ξ| + a) ^ b)) ?_)
    refine Filter.Eventually.of_forall (fun j => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), hform]
    have hstep : (1 + |ξ - (j:ℝ) / a|) ^ (-b) ≤
        (1 + a * |ξ| + a) ^ b * (1 + |(j:ℝ)|) ^ (-b) := by
      refine shannon_rpow_affine_bound hb0 hL2pos ?_
      have h3 : |(j:ℝ)| ≤ a * (|ξ - (j:ℝ) / a| + |ξ|) := by
        have h : (j:ℝ) = a * ((j:ℝ) / a) := by
          rw [div_eq_mul_inv, ← mul_assoc, mul_comm a ((j:ℝ)), mul_assoc,
            mul_inv_cancel₀ ha.ne', mul_one]
        conv_lhs => rw [h]
        rw [abs_mul, abs_of_pos ha]
        calc a * |(j:ℝ) / a| = a * |((j:ℝ) / a - ξ) + ξ| := by
              congr 1
              rw [sub_add_cancel]
          _ ≤ a * (|(j:ℝ) / a - ξ| + |ξ|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) ha.le
          _ = a * (|ξ - (j:ℝ) / a| + |ξ|) := by rw [abs_sub_comm]
      have h3' : a * (|ξ - (j:ℝ) / a| + |ξ|) = a * |ξ| + a * |ξ - (j:ℝ) / a| := by
        ring
      have h6a : 1 + |(j:ℝ)| ≤ 1 + a * |ξ| + a * |ξ - (j:ℝ) / a| := by
        linarith [h3, h3']
      have h6b : 1 + a * |ξ| + a * |ξ - (j:ℝ) / a| ≤
          (1 + a * |ξ| + a) * (1 + |ξ - (j:ℝ) / a|) := by
        have h8 : a * |ξ - (j:ℝ) / a| ≤ (1 + a * |ξ| + a) * |ξ - (j:ℝ) / a| := by
          have h8' : a ≤ 1 + a * |ξ| + a := by
            have h8'' : (0:ℝ) ≤ a * |ξ| := mul_nonneg ha.le (abs_nonneg ξ)
            linarith
          exact mul_le_mul_of_nonneg_right h8' (abs_nonneg _)
        have h9 : (1 + a * |ξ| + a) * (1 + |ξ - (j:ℝ) / a|) =
            (1 + a * |ξ| + a) + (1 + a * |ξ| + a) * |ξ - (j:ℝ) / a| := by ring
        rw [h9]
        linarith [h8, ha.le, abs_nonneg ξ]
      linarith [h6a, h6b]
    calc ‖((a : ℂ))⁻¹ * (𝐞 (-((j:ℝ) / a * c)) : ℂ) * 𝓕 k (ξ - (j:ℝ) / a)‖
        = ‖((a : ℂ))⁻¹‖ * ‖𝓕 k (ξ - (j:ℝ) / a)‖ := by
          rw [norm_mul, norm_mul, shannon_norm_fourierChar, mul_one]
      _ ≤ ‖((a : ℂ))⁻¹‖ * (C * (1 + |ξ - (j:ℝ) / a|) ^ (-b)) :=
          mul_le_mul_of_nonneg_left (hFd _) (by positivity)
      _ = (‖((a : ℂ))⁻¹‖ * C) * (1 + |ξ - (j:ℝ) / a|) ^ (-b) := by ring
      _ ≤ (‖((a : ℂ))⁻¹‖ * C) * ((1 + a * |ξ| + a) ^ b * (1 + |(j:ℝ)|) ^ (-b)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (‖((a : ℂ))⁻¹‖ * (C * (1 + a * |ξ| + a) ^ b)) * (1 + |(j:ℝ)|) ^ (-b) := by ring
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hψcont hb hψd hψsum 0
  have hP' : (∑' n : ℤ, ψ (n:ℝ)) =
      ∑' n : ℤ, 𝓕 ψ (n:ℝ) * (fourier n) ((0:ℝ) : UnitAddCircle) := by
    simpa using hP
  have hone : ∀ j : ℤ, (fourier j) ((0:ℝ) : UnitAddCircle) = 1 := by
    intro j
    rw [fourier_coe_apply]
    simp
  have h2 : (∑' n : ℤ, 𝓕 ψ (n:ℝ) * (fourier n) ((0:ℝ) : UnitAddCircle)) =
      ∑' n : ℤ, 𝓕 ψ (n:ℝ) := by
    apply tsum_congr
    intro n
    rw [hone n, mul_one]
  have hmain : (∑' j : ℤ, 𝓕 ψ (j:ℝ)) = ((a : ℂ))⁻¹ * ∑' j : ℤ,
      𝓕 k (ξ - (j : ℝ) / a) * (𝐞 (-((j : ℝ) / a * c)) : ℂ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [hform j]
    ring
  have h1 : (∑' m : ℤ, k (c - a * (m:ℝ)) * (𝐞 (-(ξ * (c - a * (m:ℝ)))) : ℂ))
      = ∑' m : ℤ, ψ (m:ℝ) := by
    apply tsum_congr
    intro m
    rw [hψdef]
  exact h1.trans (hP'.trans (h2.trans hmain))

/-- **Sublattice Shannon reproduction.**  For `β > 0`, `q ≥ 1` with `β q < 1/2` and any
`r₀ : ℤ` there is a summable kernel `K : ℤ → ℂ` reproducing every integrable continuous
function `γ` whose Fourier transform is supported in `[-β,β]` from its samples on the
coset `q ℤ + r₀`. -/
theorem sublatticeShannonReproduction (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : 0 < q)
    (hβq : β * (q : ℝ) < 1 / 2) (r₀ : ℤ) :
    ∃ K : ℤ → ℂ, Summable (fun m : ℤ => ‖K m‖) ∧
      ∀ (G : ℤ → ℂ) (γ : ℝ → ℂ), MeasureTheory.Integrable γ → Continuous γ →
        (∀ m : ℤ, γ (m : ℝ) = G m) →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → FourierTransform.fourier γ ξ = 0) →
        ∀ x : ℤ, G x = ∑' m : ℤ, G (q * m + r₀) * K (x - (q * m + r₀)) := by
  obtain ⟨dc, hβdc, hdcq, χ, hχ1, hχ0⟩ := shannon_exists_bump β hβ q hq hβq
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hβ1 : β < 1 / (2 * (q:ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hβq]
  have h2q : (1:ℝ)/(2*(q:ℝ)) + 1/(2*(q:ℝ)) = 1/(q:ℝ) := by
    field_simp
    ring
  set kS : 𝓢(ℝ, ℂ) := 𝓕⁻ ((q : ℂ) • χ) with hkSdef
  set K : ℤ → ℂ := fun n => (kS : ℝ → ℂ) (n : ℝ) with hKdef
  have hFk : (𝓕 (kS : ℝ → ℂ)) = fun y : ℝ => (q : ℂ) * (χ : ℝ → ℂ) y := by
    have h1 : 𝓕 kS = (q : ℂ) • χ := by rw [hkSdef]; simp
    rw [← SchwartzMap.fourier_coe kS, h1]
    funext y
    simp [smul_eq_mul]
  obtain ⟨Ck, hCk, hkbd⟩ := shannon_schwartz_bound kS
  obtain ⟨CF, hCF, hFbd⟩ := shannon_schwartz_bound ((q : ℂ) • χ)
  have hFbd' : ∀ y : ℝ, ‖(𝓕 (kS : ℝ → ℂ)) y‖ ≤ CF * (1 + |y|) ^ (-(2:ℝ)) := by
    intro y
    rw [hFk]
    simpa [smul_eq_mul] using hFbd y
  set C : ℝ := max Ck CF with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; exact le_trans hCk (le_max_left _ _)
  have hkbdC : ∀ x : ℝ, ‖(kS : ℝ → ℂ) x‖ ≤ C * (1 + |x|) ^ (-(2:ℝ)) := by
    intro x
    rw [hCdef]
    exact (hkbd x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _))
  have hFbdC : ∀ y : ℝ, ‖(𝓕 (kS : ℝ → ℂ)) y‖ ≤ C * (1 + |y|) ^ (-(2:ℝ)) := by
    intro y
    rw [hCdef]
    exact (hFbd' y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (by positivity) _))
  have hKsum : Summable (fun n : ℤ => ‖K n‖) := by
    have hdec := (SchwartzMap.isBigO_cocompact_rpow kS (-(2:ℝ))).comp_tendsto
      Int.tendsto_coe_cofinite
    have h1 : Summable (fun n : ℤ => ‖(n:ℝ)‖ ^ (-(2:ℝ))) := by
      simpa [Real.norm_eq_abs] using Real.summable_abs_int_rpow (b := 2) (by norm_num)
    have h2 : Summable (fun n : ℤ => (kS : ℝ → ℂ) (n:ℝ)) := summable_of_isBigO h1 hdec
    have h3 : (fun n : ℤ => ‖K n‖) = fun n : ℤ => ‖(kS : ℝ → ℂ) (n:ℝ)‖ := by
      funext n; rw [hKdef]
    rw [h3]
    exact h2.norm
  refine ⟨K, hKsum, ?_⟩
  intro G γ hγint hγcont hGγ hsupp x
  obtain ⟨hFint, hInv⟩ := shannon_bandlimited_inversion β γ hγint hγcont hsupp
  have hcontF : Continuous (𝓕 γ) := by
    change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) γ)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hγint
  set s : ℤ → ℝ := fun m => (((q * m + r₀ : ℤ)) : ℝ) with hsdef
  set t : ℤ → ℝ := fun m => (x : ℝ) - s m with htdef
  have ht_eq : ∀ m : ℤ, t m = (x:ℝ) - (((q*m+r₀:ℤ)):ℝ) := by
    intro m; rw [htdef, hsdef]
  have hcoset : Summable (fun m : ℤ => ‖(kS : ℝ → ℂ) (t m)‖) := by
    have hinj : Function.Injective (fun m : ℤ => x - (q * m + r₀)) := by
      have hinj1 : Function.Injective (fun m : ℤ => (q:ℤ) * m + r₀) := by
        intro m1 m2 h
        have h2 : (q:ℤ) * m1 = (q:ℤ) * m2 := add_right_cancel h
        exact mul_left_cancel₀ (by exact_mod_cast hq.ne' : ((q:ℤ)) ≠ 0) h2
      have hinj2 : Function.Injective (fun y : ℤ => x - y) := by
        intro a b h
        change x - a = x - b at h
        omega
      exact hinj2.comp hinj1
    have h1 := hKsum.comp_injective hinj
    have h2 : ((fun n : ℤ => ‖K n‖) ∘ fun m : ℤ => x - (q * m + r₀)) =
        fun m : ℤ => ‖(kS : ℝ → ℂ) (t m)‖ := by
      funext m
      simp only [Function.comp_apply, hKdef, ht_eq m]
      have harg : (x:ℝ) - (((q*m+r₀:ℤ)):ℝ) = (((x - (q*m+r₀) : ℤ)):ℝ) := by push_cast; ring
      rw [harg]
    rwa [h2] at h1
  have hexp_cont : ∀ m : ℤ, Continuous fun η : ℝ => (𝐞 (η * s m) : ℂ) := fun m =>
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))
  have hFcont : ∀ m : ℤ,
      Continuous (fun η : ℝ => (𝐞 (η * s m) : ℂ) * (𝓕 γ) η * (kS : ℝ → ℂ) (t m)) :=
    fun m => ((hexp_cont m).mul hcontF).mul continuous_const
  have hkey : ∀ η : ℝ, η ∈ Set.Icc (-β) β →
      (∑' m : ℤ, (𝐞 (η * s m) : ℂ) * (kS : ℝ → ℂ) (t m)) = (𝐞 (η * (x : ℝ)) : ℂ) := by
    intro η hη
    have hdec := shannon_decimation_poisson (k := (kS : ℝ → ℂ)) kS.continuous (b := 2) (C := C)
      (by norm_num) hC hkbdC hFbdC (a := (q:ℝ)) hqR ((x:ℝ) - (r₀:ℝ)) η
    have hsingle : ∀ j : ℤ, j ≠ 0 → (𝓕 (kS : ℝ → ℂ)) (η - (j:ℝ)/(q:ℝ)) *
        (𝐞 (-((j:ℝ)/(q:ℝ) * ((x:ℝ) - (r₀:ℝ)))) : ℂ) = 0 := by
      intro j hj
      rw [hFk]
      have hz : (χ : ℝ → ℂ) (η - (j:ℝ)/(q:ℝ)) = 0 := by
        apply hχ0
        have hj1 : (1:ℝ) ≤ |(j:ℝ)| := by
          have h1 : (0:ℤ) < |j| := abs_pos.mpr hj
          have h2 : (1:ℤ) ≤ |j| := by omega
          exact_mod_cast h2
        have h2' : (1:ℝ)/(q:ℝ) - β ≤ |η - (j:ℝ)/(q:ℝ)| := by
          have h := abs_add_le ((j:ℝ)/(q:ℝ) - η) η
          have he : (j:ℝ)/(q:ℝ) - η + η = (j:ℝ)/(q:ℝ) := by ring
          rw [he, abs_div, abs_of_pos hqR] at h
          have h3 : (1:ℝ)/(q:ℝ) ≤ |(j:ℝ)|/(q:ℝ) :=
            div_le_div_of_nonneg_right hj1 hqR.le
          have h4 : |η| ≤ β := abs_le.mpr hη
          have h5 : |η - (j:ℝ)/(q:ℝ)| = |((j:ℝ)/(q:ℝ) - η)| := abs_sub_comm _ _
          linarith
        have h7 : dc < (1:ℝ)/(q:ℝ) - β := by
          have h8 : β + dc < 1/(q:ℝ) := by linarith [hβ1, hdcq, h2q]
          linarith
        linarith
      simp only [hz, mul_zero, zero_mul]
    have hR : (∑' j : ℤ, (𝓕 (kS : ℝ → ℂ)) (η - (j:ℝ)/(q:ℝ)) *
        (𝐞 (-((j:ℝ)/(q:ℝ) * ((x:ℝ) - (r₀:ℝ)))) : ℂ)) = (q : ℂ) := by
      calc (∑' j : ℤ, (𝓕 (kS : ℝ → ℂ)) (η - (j:ℝ)/(q:ℝ)) *
            (𝐞 (-((j:ℝ)/(q:ℝ) * ((x:ℝ) - (r₀:ℝ)))) : ℂ))
          = (𝓕 (kS : ℝ → ℂ)) (η - (((0:ℤ)):ℝ)/(q:ℝ)) *
            (𝐞 (-(((((0:ℤ)):ℝ)/(q:ℝ)) * ((x:ℝ) - (r₀:ℝ)))) : ℂ) :=
              tsum_eq_single (0:ℤ) hsingle
        _ = (q : ℂ) := by
              rw [hFk]
              have h1 : (χ : ℝ → ℂ) η = 1 := hχ1 η hη
              simp [h1]
    have hD : (∑' m : ℤ, (kS : ℝ → ℂ) (t m) * (𝐞 (-(η * t m)) : ℂ)) = 1 := by
      have hD' : (∑' m : ℤ, (kS : ℝ → ℂ) ((x:ℝ) - (r₀:ℝ) - (q:ℝ)*(m:ℝ)) *
          (𝐞 (-(η * ((x:ℝ) - (r₀:ℝ) - (q:ℝ)*(m:ℝ)))) : ℂ)) = 1 := by
        rw [hdec, hR]
        have hqC : ((q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hqR.ne'
        rw [← Complex.ofReal_natCast]
        exact inv_mul_cancel₀ hqC
      rw [← hD']
      apply tsum_congr
      intro m
      have harg : t m = (x:ℝ) - (r₀:ℝ) - (q:ℝ)*(m:ℝ) := by
        rw [ht_eq m]; push_cast; ring
      rw [harg]
    have h1 : (∑' m : ℤ, (𝐞 (η * s m) : ℂ) * (kS : ℝ → ℂ) (t m))
        = (𝐞 (η * (x:ℝ)) : ℂ) * (∑' m : ℤ, (kS : ℝ → ℂ) (t m) *
            (𝐞 (-(η * t m)) : ℂ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      have hs : s m = (x:ℝ) - t m := by rw [htdef, hsdef]; ring
      have harg : η * ((x:ℝ) - t m) = η * (x:ℝ) + -(η * t m) := by ring
      rw [hs, harg, ← shannon_fourierChar_mul]
      ring
    rw [h1, hD, mul_one]
  have hpt : ∀ η : ℝ, (∑' m : ℤ, (𝐞 (η * s m) : ℂ) * (𝓕 γ) η * (kS : ℝ → ℂ) (t m))
      = (𝓕 γ) η * (𝐞 (η * (x : ℝ)) : ℂ) := by
    intro η
    by_cases hη : η ∈ Set.Icc (-β) β
    · calc (∑' m : ℤ, (𝐞 (η * s m) : ℂ) * (𝓕 γ) η * (kS : ℝ → ℂ) (t m))
          = (𝓕 γ) η * (∑' m : ℤ, (𝐞 (η * s m) : ℂ) * (kS : ℝ → ℂ) (t m)) := by
            rw [← tsum_mul_left]
            apply tsum_congr; intro m; ring
        _ = (𝓕 γ) η * (𝐞 (η * (x:ℝ)) : ℂ) := by rw [hkey η hη]
    · rw [hsupp η hη]
      simp
  have hbound : ∀ (m : ℤ) (η : ℝ), ‖(𝐞 (η * s m) : ℂ) * (𝓕 γ) η * (kS : ℝ → ℂ) (t m)‖
      ≤ ‖(𝓕 γ) η‖ * ‖(kS : ℝ → ℂ) (t m)‖ := by
    intro m η
    rw [norm_mul, norm_mul, shannon_norm_fourierChar, one_mul]
  have hbsummable : ∀ η : ℝ, Summable (fun m : ℤ => ‖(𝓕 γ) η‖ * ‖(kS : ℝ → ℂ) (t m)‖) :=
    fun η => hcoset.mul_left _
  have hbint : Integrable (fun η : ℝ => ∑' m : ℤ, ‖(𝓕 γ) η‖ * ‖(kS : ℝ → ℂ) (t m)‖) := by
    have h1 : (fun η : ℝ => ∑' m : ℤ, ‖(𝓕 γ) η‖ * ‖(kS : ℝ → ℂ) (t m)‖)
        = fun η : ℝ => ‖(𝓕 γ) η‖ * (∑' m : ℤ, ‖(kS : ℝ → ℂ) (t m)‖) := by
      funext η
      rw [tsum_mul_left]
    rw [h1]
    exact hFint.norm.mul_const _
  have hHasSum : HasSum (fun m : ℤ => ∫ η : ℝ,
        (𝐞 (η * s m) : ℂ) * (𝓕 γ) η * (kS : ℝ → ℂ) (t m))
      (∫ η : ℝ, (𝓕 γ) η * (𝐞 (η * (x:ℝ)) : ℂ)) :=
    hasSum_integral_of_dominated_convergence
      (fun (m : ℤ) (η : ℝ) => ‖(𝓕 γ) η‖ * ‖(kS : ℝ → ℂ) (t m)‖)
      (fun m => (hFcont m).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall (hbound m))
      (Filter.Eventually.of_forall hbsummable)
      hbint
      (Filter.Eventually.of_forall (fun η => by
        have hs : Summable (fun m : ℤ =>
            (𝐞 (η * s m) : ℂ) * (𝓕 γ) η * (kS : ℝ → ℂ) (t m)) :=
          Summable.of_norm_bounded (hbsummable η) (fun m => hbound m η)
        have h := hs.hasSum
        rwa [hpt η] at h))
  have hmain : HasSum (fun m : ℤ => γ (s m) * (kS : ℝ → ℂ) (t m)) (γ (x:ℝ)) := by
    convert hHasSum using 1
    · funext m
      have h1 : (∫ η : ℝ, (𝐞 (η * s m) : ℂ) * (𝓕 γ) η) = γ (s m) := (hInv (s m)).symm
      rw [integral_mul_const, h1]
    · rw [hInv (x:ℝ)]
      apply integral_congr_ae
      filter_upwards with η
      ring
  have hgoal : (∑' m : ℤ, G (q * m + r₀) * K (x - (q * m + r₀))) = γ (x:ℝ) := by
    rw [← hmain.tsum_eq]
    apply tsum_congr
    intro m
    have h1 : γ (s m) = G (q * m + r₀) := by rw [hsdef]; exact hGγ (q * m + r₀)
    have h2 : (kS : ℝ → ℂ) (t m) = K (x - (q * m + r₀)) := by
      rw [hKdef]
      congr 1
      rw [ht_eq m]
      push_cast
      ring
    rw [h1, h2]
  rw [hgoal, hGγ x]

end

end Work.KMTAreas.A7
