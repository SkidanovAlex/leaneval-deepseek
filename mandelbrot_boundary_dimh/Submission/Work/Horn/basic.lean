import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# AREA HORN — cheap formal layer

Basic consequences of the `ParabData` / `HornData` interfaces: the lifted horn map
`E = Φ ∘ φ` is `T`-equivariant on `DE`, the ends behave as filters, and `pushdown` of a
`T`-equivariant map is the induced map on the cylinder `ℂ/ℤ ≅ ℂ*`.

Everything here is proved from the interface fields alone (`ParabData` axioms).
-/

namespace Work.Horn

noncomputable section

open MandelDim Filter Topology Metric
open scoped Topology

namespace MandelDim

/-! ## The lifted horn map on `DE` -/

namespace ParabData

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

theorem mem_DE (d : ParabData f₀ D₀) {w : ℂ} :
    w ∈ d.DE ↔ w ∈ d.Dφ ∧ d.φ w ∈ ParabolicBasin f₀ D₀ := Iff.rfl

/-- `E = Φ ∘ φ` is `T`-equivariant on `DE`. -/
theorem E_add_one (d : ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) (hw1 : w + 1 ∈ d.DE) :
    d.E (w + 1) = d.E w + 1 := by
  rw [mem_DE] at hw hw1
  simp only [ParabData.E]
  rw [d.φ_abel w hw.1 hw1.1, d.Φ_abel (d.φ w) hw.2]

/-- Upper end: `E w - w → 0` as `Im w → +∞`. -/
theorem E_upper_iff (d : ParabData f₀ D₀) :
    ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < w.im → ‖d.E w - w‖ < ε := by
  intro ε hε
  have hmem : ∀ᶠ x : ℂ in upperEnd, dist (d.Φ (d.φ x) - x) 0 < ε :=
    d.E_upper.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)
  rw [MandelDim.upperEnd, Filter.eventually_iff, Filter.mem_comap] at hmem
  obtain ⟨t, ht, hts⟩ := hmem
  rw [Filter.mem_atTop_sets] at ht
  obtain ⟨R, hR⟩ := ht
  refine ⟨R, fun w hw => ?_⟩
  have h1 : w.im ∈ t := hR w.im hw.le
  have h2 : w ∈ Complex.im ⁻¹' t := h1
  have h3 := hts h2
  simpa [ParabData.E, dist_eq_norm, sub_zero] using h3

/-- Lower end: `E w - w` has a limit as `Im w → -∞`. -/
theorem E_lower_iff (d : ParabData f₀ D₀) :
    ∃ cl : ℂ, ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < -R → ‖d.E w - w - cl‖ < ε := by
  obtain ⟨cl, hcl⟩ := d.E_lower
  refine ⟨cl, fun ε hε => ?_⟩
  have hmem : ∀ᶠ x : ℂ in lowerEnd, dist (d.Φ (d.φ x) - x) cl < ε :=
    hcl.eventually (Metric.ball_mem_nhds cl hε)
  rw [MandelDim.lowerEnd, Filter.eventually_iff, Filter.mem_comap] at hmem
  obtain ⟨t, ht, hts⟩ := hmem
  rw [Filter.mem_atBot_sets] at ht
  obtain ⟨R, hR⟩ := ht
  refine ⟨-R, fun w hw => ?_⟩
  have h1 : w.im ∈ t := hR w.im (by linarith)
  have h2 : w ∈ Complex.im ⁻¹' t := h1
  have h3 := hts h2
  simpa [ParabData.E, dist_eq_norm] using h3

end ParabData

/-! ## `π(w) = exp(2πiw)` -/

theorem piExp_ne_zero (w : ℂ) : piExp w ≠ 0 := Complex.exp_ne_zero _

theorem piExp_add_one (w : ℂ) : piExp (w + 1) = piExp w := by
  rw [piExp, piExp,
    show 2 * ↑Real.pi * Complex.I * (w + 1) =
      2 * ↑Real.pi * Complex.I * w + 2 * ↑Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem piExp_add_natCast (v : ℂ) (n : ℕ) : piExp (v + n) = piExp v := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [show v + ((m + 1 : ℕ) : ℂ) = (v + m) + 1 by push_cast; ring, piExp_add_one, ih]

theorem piExp_sub_natCast (v : ℂ) (n : ℕ) : piExp (v - n) = piExp v := by
  have h := piExp_add_natCast (v - n) n
  rw [show v - (n : ℂ) + n = v by ring] at h
  exact h.symm

theorem piExp_add_intCast (v : ℂ) (k : ℤ) : piExp (v + k) = piExp v := by
  rcases k with n | n
  · exact piExp_add_natCast v n
  · rw [show v + Int.negSucc n = v - ((n + 1 : ℕ) : ℂ) by push_cast [Int.negSucc]; ring]
    exact piExp_sub_natCast v (n + 1)

/-- Two points have the same `π`-image iff they differ by an integer. -/
theorem piExp_eq_iff {u v : ℂ} : piExp u = piExp v ↔ ∃ k : ℤ, u = v + k := by
  constructor
  · intro h
    simp only [MandelDim.piExp] at h
    have h2 : Complex.exp (2 * ↑Real.pi * Complex.I * u - (2 * ↑Real.pi * Complex.I * v)) = 1 := by
      rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have hne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h3 : 2 * ↑Real.pi * Complex.I * (u - v) = 2 * ↑Real.pi * Complex.I * (n : ℂ) := by
      rw [show 2 * ↑Real.pi * Complex.I * u - 2 * ↑Real.pi * Complex.I * v =
        2 * ↑Real.pi * Complex.I * (u - v) by ring] at hn
      rw [hn]; ring
    linear_combination mul_left_cancel₀ hne h3
  · rintro ⟨k, rfl⟩
    exact piExp_add_intCast v k

theorem piExp_log_div (ζ : ℂ) (hζ : ζ ≠ 0) :
    piExp (Complex.log ζ / (2 * Real.pi * Complex.I)) = ζ := by
  rw [piExp,
    show 2 * ↑Real.pi * Complex.I * (Complex.log ζ / (2 * ↑Real.pi * Complex.I)) =
      Complex.log ζ by field_simp,
    Complex.exp_log hζ]

/-! ## `T`-invariant sets and the integers -/

theorem IsTInvariant.add_int {D : Set ℂ} (hD : IsTInvariant D) {w : ℂ} (hw : w ∈ D)
    (k : ℤ) : w + k ∈ D := by
  induction k using Int.induction_on with
  | zero => simpa using hw
  | succ n ih =>
      have hEq : w + (((n : ℤ) + 1 : ℤ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
      rw [hEq]
      exact (hD (w + (n : ℂ))).mp ih
  | pred n ih =>
      have hEq : w + (((-(n : ℤ) - 1 : ℤ)) : ℂ) = (w + (-(n : ℂ))) - 1 := by push_cast; ring
      rw [hEq]
      exact (hD ((w + (-(n : ℂ))) - 1)).mpr (by simpa using ih)

/-- `E`-equivariance iterated in the positive direction. -/
theorem E_add_nat {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) (n : ℕ) :
    E (w + n) = E w + n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : w + (m : ℂ) ∈ D := by
        simpa using IsTInvariant.add_int hD hw (m : ℤ)
      have hEq : w + ((m + 1 : ℕ) : ℂ) = (w + (m : ℂ)) + 1 := by push_cast; ring
      have hmem1 : (w + (m : ℂ)) + 1 ∈ D := by
        rw [← hEq]
        simpa using IsTInvariant.add_int hD hw (((m + 1 : ℕ)) : ℤ)
      rw [hEq, hE (w + (m : ℂ)) hmem hmem1, ih]
      push_cast; ring

/-- `E`-equivariance iterated in the negative direction. -/
theorem E_sub_nat {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) (n : ℕ) :
    E (w - n) = E w - n := by
  have hmem : w - (n : ℂ) ∈ D := by
    have h := IsTInvariant.add_int hD hw (-(n : ℤ))
    rw [show w + (((-(n : ℤ)) : ℤ) : ℂ) = w - (n : ℂ) by push_cast; ring] at h
    exact h
  have h1 := E_add_nat hD hE hmem n
  rw [show w - (n : ℂ) + (n : ℂ) = w by ring] at h1
  rw [h1]; ring

/-- `E`-equivariance iterated over the integers. -/
theorem E_add_int {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) (k : ℤ) :
    E (w + k) = E w + k := by
  rcases k with n | n
  · simpa using E_add_nat hD hE hw n
  · rw [show w + Int.negSucc n = w - ((n + 1 : ℕ) : ℂ) by push_cast [Int.negSucc]; ring]
    rw [E_sub_nat hD hE hw (n + 1)]
    push_cast [Int.negSucc]; ring

/-! ## `pushdown` -/

theorem pushdown_zero (E : ℂ → ℂ) : pushdown E 0 = 0 := by simp [pushdown]

theorem pushdown_of_ne (E : ℂ → ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    pushdown E ζ = piExp (E (Complex.log ζ / (2 * Real.pi * Complex.I))) := by
  simp [pushdown, hζ]

/-- `pushdown` of a `T`-equivariant map is independent of the chosen lift: it is the induced
map on the cylinder. -/
theorem pushdown_piExp {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) :
    pushdown E (piExp w) = piExp (E w) := by
  have hζ : piExp w ≠ 0 := piExp_ne_zero w
  rw [pushdown_of_ne E hζ]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Complex.log (piExp w) / (2 * Real.pi * Complex.I) = w + k := by
    refine (piExp_eq_iff).mp ?_
    rw [piExp_log_div (piExp w) hζ]
  rw [hk, E_add_int hD hE hw k, piExp_add_intCast]


theorem piExp_sub (a b : ℂ) : piExp (a - b) = piExp a / piExp b := by
  rw [piExp, piExp, piExp, ← Complex.exp_sub,
    show 2 * ↑Real.pi * Complex.I * (a - b) =
      2 * ↑Real.pi * Complex.I * a - 2 * ↑Real.pi * Complex.I * b by ring]

/-- The map `ζ ↦ log ζ/(2πi)` tends to the upper end as `ζ → 0`. -/
theorem tendsto_log_div_upperEnd :
    Tendsto (fun ζ : ℂ => Complex.log ζ / (2 * ↑Real.pi * Complex.I)) (𝓝[≠] (0 : ℂ))
      upperEnd := by
  rw [MandelDim.upperEnd, Filter.tendsto_comap_iff, Filter.tendsto_atTop]
  intro R
  have hball : ball (0 : ℂ) (Real.exp (-(2 * Real.pi * R))) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (Real.exp_pos _)
  have hmem : ball (0 : ℂ) (Real.exp (-(2 * Real.pi * R))) ∩ ({0}ᶜ) ∈ 𝓝[≠] (0 : ℂ) := by
    rw [nhdsWithin]
    exact Filter.inter_mem_inf hball (Filter.mem_principal_self _)
  refine Filter.mem_of_superset hmem ?_
  intro ζ hζ
  obtain ⟨hballmem, hne⟩ := hζ
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hballmem
  simp only [Set.mem_setOf_eq]
  change R ≤ (Complex.log ζ / (2 * ↑Real.pi * Complex.I)).im
  have him : (Complex.log ζ / (2 * ↑Real.pi * Complex.I)).im =
      -(Real.log ‖ζ‖) / (2 * Real.pi) := by
    rw [Complex.div_im, Complex.log_re, Complex.log_im]
    have h1 : (2 * ↑Real.pi * Complex.I : ℂ).re = 0 := by simp
    have h2 : (2 * ↑Real.pi * Complex.I : ℂ).im = 2 * Real.pi := by simp
    have h3 : Complex.normSq ((2 : ℂ) * ↑Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
      rw [show ((2 : ℂ) * ↑Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
      rw [Complex.normSq_apply]
      simp
      ring
    rw [h1, h2, h3]
    field_simp
    ring
  rw [him]
  have hlog : Real.log ‖ζ‖ < -(2 * Real.pi * R) := by
    have h1 : Real.log ‖ζ‖ < Real.log (Real.exp (-(2 * Real.pi * R))) :=
      Real.log_lt_log (norm_pos_iff.mpr hne) hballmem
    simpa using h1
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h3 : Real.log ‖ζ‖ / (2 * Real.pi) < (-(2 * Real.pi * R)) / (2 * Real.pi) :=
    div_lt_div_of_pos_right hlog h2pi
  have h4 : (-(2 * Real.pi * R)) / (2 * Real.pi) = -R := by field_simp
  rw [h4] at h3
  simpa [neg_div] using neg_le_neg h3.le

/-- HORN field `g_deriv`: `pushdown Ẽ` has derivative `1` at `0` (normalization (4.1.5)). -/
theorem deriv_pushdown_E {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    deriv (pushdown d.E) 0 = 1 := by
  have hlog := tendsto_log_div_upperEnd
  have hdiff : Tendsto (fun ζ : ℂ => d.E (Complex.log ζ / (2 * ↑Real.pi * Complex.I)) -
      (Complex.log ζ / (2 * ↑Real.pi * Complex.I))) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := ParabData.E_upper_iff d ε hε
    have hset : {w : ℂ | R < w.im} ∈ upperEnd := by
      rw [MandelDim.upperEnd, Filter.mem_comap]
      refine ⟨{b : ℝ | R + 1 ≤ b}, ?_, ?_⟩
      · rw [Filter.mem_atTop_sets]; exact ⟨R + 1, fun b hb => hb⟩
      · intro z hz
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz
        simp only [Set.mem_setOf_eq]
        linarith
    filter_upwards [hlog.eventually hset] with ζ hζ
    simpa [dist_eq_norm] using hR _ hζ
  have hcomp : Tendsto (fun ζ : ℂ => piExp (d.E (Complex.log ζ / (2 * ↑Real.pi * Complex.I)) -
      (Complex.log ζ / (2 * ↑Real.pi * Complex.I)))) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hpi : Tendsto (fun z : ℂ => piExp z) (𝓝 (0 : ℂ)) (𝓝 1) := by
      have hc : Continuous piExp := by unfold piExp; fun_prop
      have h0 : piExp 0 = 1 := by simp [piExp]
      simpa [h0] using hc.tendsto 0
    exact hpi.comp hdiff
  have hquot : Tendsto (fun ζ : ℂ => ζ⁻¹ * pushdown d.E ζ) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    refine Filter.Tendsto.congr' ?_ hcomp
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    set w : ℂ := Complex.log ζ / (2 * ↑Real.pi * Complex.I) with hwdef
    have hpush : pushdown d.E ζ = piExp (d.E w) := by rw [pushdown_of_ne d.E hζ, hwdef]
    have hzeta : ζ = piExp w := by rw [hwdef]; exact (piExp_log_div ζ hζ).symm
    rw [hpush, hzeta, ← div_eq_inv_mul]
    exact piExp_sub _ _
  have hslope : HasDerivAt (pushdown d.E) 1 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hsl : slope (pushdown d.E) 0 = fun ζ : ℂ => ζ⁻¹ * pushdown d.E ζ := by
      funext ζ
      simp [slope, pushdown_zero, smul_eq_mul]
    rw [hsl]
    exact hquot
  simpa using hslope.deriv

end MandelDim

end

end Work.Horn
