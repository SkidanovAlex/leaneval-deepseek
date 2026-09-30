import Mathlib
import Submission.Work.BMF.H6_imports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory intervalIntegral
open scoped Interval

namespace Work.BMF

/-- **Cauchy–Schwarz / Jensen for interval integrals.**  For `X > 0` and a real function `g`
whose integral and integral of the square over `[X, 2X]` both exist,
`(∫_X^{2X} g)^2 ≤ X · ∫_X^{2X} g^2` (the length of `[X, 2X]` being `X`). -/
theorem CS_sq_integral_le (X : ℝ) (hX : 0 < X) (g : ℝ → ℝ)
    (hg : IntegrableOn g (Set.Ioc X (2*X)) volume)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Set.Ioc X (2*X)) volume) :
    (∫ y in X..(2*X), g y) ^ 2 ≤ X * ∫ y in X..(2*X), g y ^ 2 := by
  have hle : X ≤ 2 * X := by linarith
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    (Even.strictConvexOn_pow (show Even 2 by exact ⟨1, by norm_num⟩) (by norm_num)).convexOn
  have hmem : volume (Set.Ioc X (2*X)) = ENNReal.ofReal X := by
    rw [Real.volume_Ioc]; congr 1; ring
  have h0 : volume (Set.Ioc X (2*X)) ≠ 0 := by
    rw [hmem]; exact ENNReal.ofReal_ne_zero_iff.mpr hX
  have ht : volume (Set.Ioc X (2*X)) ≠ ⊤ := by
    rw [hmem]; exact ENNReal.ofReal_ne_top
  have hJ := ConvexOn.map_set_average_le (μ := volume) (s := Set.univ) (t := Set.Ioc X (2*X))
    (f := g) (g := fun x : ℝ => x ^ 2) hconv (by fun_prop) isClosed_univ h0 ht
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hg hg2
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul] at hJ
  have hreal : volume.real (Set.Ioc X (2*X)) = X := by
    rw [Measure.real, hmem, ENNReal.toReal_ofReal (le_of_lt hX)]
  rw [hreal] at hJ
  simp_rw [← intervalIntegral.integral_of_le hle] at hJ
  have eI : X⁻¹ * (∫ y in X..(2*X), g y) = (∫ y in X..(2*X), g y) / X := by
    rw [div_eq_inv_mul]
  have eJ : X⁻¹ * (∫ y in X..(2*X), g y ^ 2) = (∫ y in X..(2*X), g y ^ 2) / X := by
    rw [div_eq_inv_mul]
  rw [eI, eJ] at hJ
  have h := (le_div_iff₀ hX).mp hJ
  have e : ((∫ y in X..(2*X), g y) / X) ^ 2 * X = (∫ y in X..(2*X), g y) ^ 2 / X := by
    field_simp
  rw [e] at h
  rw [div_le_iff₀ hX] at h
  have h2 : (∫ y in X..(2*X), g y ^ 2) * X = X * ∫ y in X..(2*X), g y ^ 2 := by ring
  linarith [h, h2]

/-- The step function `y ↦ ∑_{n ∈ ℕ ∩ [y, y+H]} b n`, together with its squared norm, is
integrable over `[X, 2X]` for `X > 0` and arbitrary `b : ℕ → ℂ`: on `Ioc X (2X)` the summation
index always lies in the fixed finite range `[⌈X⌉₊, ⌊2X+H⌋₊]`, so the function is bounded by
`∑_{n} ‖b n‖` over that range and is a finite sum of indicators of measurable sets. -/
theorem CS_natIcc_integrableOn (b : ℕ → ℂ) (X H : ℝ) (hX : 0 < X) :
    IntegrableOn (fun y => ‖∑ n ∈ natIcc y (y+H), b n‖) (Set.Ioc X (2*X)) volume ∧
    IntegrableOn (fun y => ‖∑ n ∈ natIcc y (y+H), b n‖ ^ 2) (Set.Ioc X (2*X)) volume := by
  have hma : Measurable (fun y : ℝ => ∑ n ∈ natIcc y (y+H), b n) := by
    have hpair : Measurable (fun y : ℝ => (⌈y⌉₊, ⌊y+H⌋₊)) := by measurability
    have hF : Measurable (fun pq : ℕ × ℕ => ∑ n ∈ Finset.Icc pq.1 pq.2, b n) :=
      measurable_of_countable _
    exact hF.comp hpair
  let B : Finset ℕ := Finset.Icc ⌈X⌉₊ ⌊2*X + H⌋₊
  let C : ℝ := ∑ n ∈ B, ‖b n‖
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have hbound : ∀ y ∈ Set.Ioc X (2*X), ‖∑ n ∈ natIcc y (y+H), b n‖ ≤ C := by
    intro y hy
    have hsub : natIcc y (y+H) ⊆ B := by
      intro n hn
      have hn' : ⌈y⌉₊ ≤ n ∧ n ≤ ⌊y+H⌋₊ :=
        Finset.mem_Icc.mp (show n ∈ Finset.Icc ⌈y⌉₊ ⌊y+H⌋₊ from hn)
      refine Finset.mem_Icc.mpr ⟨le_trans (Nat.ceil_mono (le_of_lt hy.1)) hn'.1, ?_⟩
      exact le_trans hn'.2 (Nat.floor_mono (by linarith [hy.2]))
    calc ‖∑ n ∈ natIcc y (y+H), b n‖
        ≤ ∑ n ∈ natIcc y (y+H), ‖b n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ B, ‖b n‖ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => norm_nonneg _)
      _ = C := rfl
  have hfin : volume (Set.Ioc X (2*X)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  constructor
  · apply Measure.integrableOn_of_bounded (M := C) hfin hma.norm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    simpa using hbound y hy
  · apply Measure.integrableOn_of_bounded (M := C ^ 2) hfin
      ((hma.norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have h1 := hbound y hy
    have h2 := norm_nonneg (∑ n ∈ natIcc y (y+H), b n)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h1, h2, hCnn]

theorem CS_shortint (b : ℕ → ℂ) (X H η : ℝ) (hH : 0 < H) (hX : 0 < X) (hη : 0 ≤ η) :
    η * H * X ≤ ∫ y in X..(2*X), ‖∑ n ∈ Work.BMF.natIcc y (y+H), b n‖ →
    η ^ 2 ≤ (1 / X) * (∫ y in X..(2*X), ‖(1 / H) * ∑ n ∈ Work.BMF.natIcc y (y+H), b n‖ ^ 2) := by
  intro h
  let S : ℝ → ℂ := fun y => ∑ n ∈ Work.BMF.natIcc y (y+H), b n
  let G : ℝ → ℝ := fun y => ‖((1 : ℂ) / (H : ℂ)) * S y‖
  change η * H * X ≤ ∫ y in X..(2*X), ‖S y‖ at h
  change η ^ 2 ≤ (1 / X) * (∫ y in X..(2*X), G y ^ 2)
  -- pointwise norm identity
  have hpt : ∀ y, G y = (1/H) * ‖S y‖ := fun y => by
    simp only [G]
    rw [Complex.norm_mul, Complex.norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hH]
  obtain ⟨hint1, hint2⟩ := CS_natIcc_integrableOn b X H hX
  have hGint : IntegrableOn G (Set.Ioc X (2*X)) volume := by
    have h1 : IntegrableOn (fun y => (1/H) * ‖S y‖) (Set.Ioc X (2*X)) volume :=
      Integrable.const_mul hint1 (1/H)
    exact IntegrableOn.congr_fun (f := fun y => (1/H) * ‖S y‖) h1
      (fun y _ => (hpt y).symm) measurableSet_Ioc
  have hG2int : IntegrableOn (fun y => G y ^ 2) (Set.Ioc X (2*X)) volume := by
    have h1 : IntegrableOn (fun y => (1/H) ^ 2 * ‖S y‖ ^ 2) (Set.Ioc X (2*X)) volume :=
      Integrable.const_mul hint2 ((1/H) ^ 2)
    have hpt2 : ∀ y, (1/H) ^ 2 * ‖S y‖ ^ 2 = G y ^ 2 := fun y => by
      rw [hpt y]; ring
    exact IntegrableOn.congr_fun (f := fun y => (1/H) ^ 2 * ‖S y‖ ^ 2) h1
      (fun y _ => hpt2 y) measurableSet_Ioc
  have hCS := CS_sq_integral_le X hX G hGint hG2int
  have hGint_eq : (∫ y in X..(2*X), G y) = (1/H) * ∫ y in X..(2*X), ‖S y‖ := by
    calc ∫ y in X..(2*X), G y = ∫ y in X..(2*X), (1/H) * ‖S y‖ := by
          apply intervalIntegral.integral_congr
          intro y _
          exact hpt y
      _ = (1/H) * ∫ y in X..(2*X), ‖S y‖ := intervalIntegral.integral_const_mul _ _
  have hηX : η * X ≤ ∫ y in X..(2*X), G y := by
    rw [hGint_eq]
    have heq : η * X = (1/H) * (η * H * X) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hGnonneg : 0 ≤ ∫ y in X..(2*X), G y :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
  have hηXnn : 0 ≤ η * X := mul_nonneg hη (le_of_lt hX)
  have hsq : (η * X) ^ 2 ≤ (∫ y in X..(2*X), G y) ^ 2 := by
    simpa [sq] using mul_self_le_mul_self hηXnn hηX
  have hbig : (η * X) ^ 2 ≤ X * ∫ y in X..(2*X), G y ^ 2 := le_trans hsq hCS
  have hfinal : η ^ 2 ≤ (1 / X) * ∫ y in X..(2*X), G y ^ 2 := by
    rw [show (1/X) * ∫ y in X..(2*X), G y ^ 2 = (∫ y in X..(2*X), G y ^ 2) / X by ring]
    rw [le_div_iff₀ hX]
    have h2 : X * (η ^ 2 * X) ≤ X * (∫ y in X..(2*X), G y ^ 2) := by nlinarith [hbig]
    exact le_of_mul_le_mul_left h2 hX
  exact hfinal

end Work.BMF
