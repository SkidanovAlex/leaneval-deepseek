import Mathlib

namespace Work.WilE4.CAD

/-- Adding a real number of strictly smaller absolute value does not change the sign. -/
theorem sign_add_of_abs_lt {a b : ℝ} (h : |b| < |a|) :
    SignType.sign (a + b) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h1 : |b| < -a := by simpa [abs_of_neg ha] using h
    have hab : a + b < 0 := by linarith [le_abs_self b]
    rw [sign_neg hab, sign_neg ha]
  · subst ha
    have hb : (0 : ℝ) ≤ |b| := abs_nonneg b
    simp only [abs_zero] at h
    linarith
  · have h1 : |b| < a := by simpa [abs_of_pos ha] using h
    have hab : 0 < a + b := by linarith [neg_abs_le b]
    rw [sign_pos hab, sign_pos ha]

/-- The part of `p` below degree `d`, evaluated at `y`, is bounded by `d * C * |y| ^ (d - 1)`,
provided every coefficient of `p` of index at most `d` is bounded by `C ≥ 0` and `1 ≤ |y|`. -/
theorem abs_eval_sub_leadingCoeff_mul_pow_le {p : Polynomial ℝ} {d : ℕ} (hp : p.natDegree = d)
    {C : ℝ} (hC : 0 ≤ C) (hbd : ∀ j ∈ Finset.range (d + 1), |p.coeff j| ≤ C)
    {y : ℝ} (hy : 1 ≤ |y|) :
    |p.eval y - p.coeff d * y ^ d| ≤ (d : ℝ) * C * |y| ^ (d - 1) := by
  have hsum : p.eval y = (∑ i ∈ Finset.range d, p.coeff i * y ^ i) + p.coeff d * y ^ d := by
    rw [Polynomial.eval_eq_sum_range, hp, Finset.sum_range_succ]
  rw [show p.eval y - p.coeff d * y ^ d = ∑ i ∈ Finset.range d, p.coeff i * y ^ i by
    rw [hsum]; ring]
  calc |∑ i ∈ Finset.range d, p.coeff i * y ^ i|
      ≤ ∑ i ∈ Finset.range d, |p.coeff i * y ^ i| :=
        Finset.abs_sum_le_sum_abs (fun i => p.coeff i * y ^ i) (Finset.range d)
    _ = ∑ i ∈ Finset.range d, |p.coeff i| * |y| ^ i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_pow]
    _ ≤ ∑ _i ∈ Finset.range d, C * |y| ^ (d - 1) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hi' : i < d := Finset.mem_range.mp hi
        have hle : i ≤ d - 1 := by omega
        have hpow : |y| ^ i ≤ |y| ^ (d - 1) := pow_le_pow_right₀ hy hle
        exact mul_le_mul (hbd i (Finset.mem_range.mpr (by omega))) hpow (by positivity) hC
    _ = (d : ℝ) * C * |y| ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Pointwise large-argument sign statement for a single real polynomial: if `p` has degree
`d ≥ 1`, if every coefficient of `p` in `Finset.range (d+1)` is bounded by `C ≥ 0` in absolute
value, and if the `d`-th coefficient is bounded below by `ε > 0` in absolute value, then at every
`y` with `|y| ≥ max 1 (2 * d * C / ε)` the sign of `p.eval y` is `sign (p.coeff d) * (sign y)^d`. -/
theorem sign_eval_of_coeff_bound {p : Polynomial ℝ} {d : ℕ} (hd : 1 ≤ d) (hp : p.natDegree = d)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hbd : ∀ j ∈ Finset.range (d + 1), |p.coeff j| ≤ C) (hc : ε ≤ |p.coeff d|)
    {y : ℝ} (hy : max 1 (2 * (d : ℝ) * C / ε) ≤ |y|) :
    SignType.sign (p.eval y) = SignType.sign (p.coeff d) * SignType.sign y ^ d := by
  have hy1 : 1 ≤ |y| := le_trans (le_max_left _ _) hy
  have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy1
  have h2 : 2 * (d : ℝ) * C / ε ≤ |y| := le_trans (le_max_right _ _) hy
  have h2' : 2 * (d : ℝ) * C ≤ ε * |y| := by
    have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hε)
    rw [div_mul_cancel₀ _ (ne_of_gt hε), mul_comm |y| ε] at h
    exact h
  have hdc : (d : ℝ) * C < ε * |y| := by
    rcases eq_or_lt_of_le (mul_nonneg (Nat.cast_nonneg d) hC) with h0 | h0
    · rw [← h0]; exact mul_pos hε hypos
    · nlinarith [h2']
  have hlt : |p.eval y - p.coeff d * y ^ d| < |p.coeff d * y ^ d| := by
    have hb := abs_eval_sub_leadingCoeff_mul_pow_le hp hC hbd hy1
    have hp2 : 0 < |y| ^ (d - 1) := pow_pos hypos _
    have h3 : (d : ℝ) * C * |y| ^ (d - 1) < ε * |y| ^ d := by
      have h3' := mul_lt_mul_of_pos_right hdc hp2
      have hpow : |y| ^ d = |y| ^ (d - 1) * |y| := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      nlinarith [h3']
    have h4 : ε * |y| ^ d ≤ |p.coeff d * y ^ d| := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have hmain : SignType.sign (p.eval y) = SignType.sign (p.coeff d * y ^ d) := by
    have heq : p.eval y = p.coeff d * y ^ d + (p.eval y - p.coeff d * y ^ d) := by ring
    rw [heq, sign_add_of_abs_lt hlt]
  rw [hmain, sign_mul, sign_pow]

/-- Local uniform coefficient bounds: a family of real polynomials whose coefficients are
continuous in the parameter and whose degree equals `d ≥ 1` eventually near `x₀` admits a
neighbourhood `W` of `x₀` on which the degree is `d`, the `d`-th coefficient is bounded below in
absolute value by a fixed `ε > 0`, and all coefficients in `Finset.range (d+1)` are bounded by a
fixed `C ≥ 0`. -/
theorem nhds_coeff_bounds_local {X : Type*} [TopologicalSpace X] (Q : X → Polynomial ℝ)
    (hcont : ∀ j, Continuous fun x => (Q x).coeff j) {x₀ : X} {d : ℕ} (hd : 1 ≤ d)
    (hdeg : ∀ᶠ x in nhds x₀, (Q x).natDegree = d) :
    ∃ W ∈ nhds x₀, ∃ ε > 0, ∃ C, 0 ≤ C ∧ ∀ x ∈ W,
      (Q x).natDegree = d ∧ ε ≤ |(Q x).coeff d| ∧
        ∀ j ∈ Finset.range (d + 1), |(Q x).coeff j| ≤ C := by
  have hx0 : (Q x₀).natDegree = d := hdeg.self_of_nhds
  have hne : (Q x₀).coeff d ≠ 0 := by
    have hp0 : Q x₀ ≠ 0 := by
      intro h0
      have hz : (Q x₀).natDegree = 0 := by rw [h0]; simp
      omega
    have hcoeff : (Q x₀).coeff d = (Q x₀).leadingCoeff := by
      rw [← hx0, Polynomial.coeff_natDegree]
    rw [hcoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have habs : 0 < |(Q x₀).coeff d| := abs_pos.mpr hne
  have hεpos : 0 < |(Q x₀).coeff d| / 2 := by linarith
  have hCnn : 0 ≤ ∑ j ∈ Finset.range (d + 1), (|(Q x₀).coeff j| + 1) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hevε : ∀ᶠ x in nhds x₀, |(Q x₀).coeff d| / 2 ≤ |(Q x).coeff d| := by
    have hlt : |(Q x₀).coeff d| / 2 < |(Q x₀).coeff d| := by linarith
    filter_upwards
      [(hcont d).abs.continuousAt.eventually_mem (isOpen_Ioi.mem_nhds hlt)] with x hx
    exact le_of_lt hx
  have hevC : ∀ᶠ x in nhds x₀, ∀ j ∈ Finset.range (d + 1),
      |(Q x).coeff j| ≤ ∑ j' ∈ Finset.range (d + 1), (|(Q x₀).coeff j'| + 1) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hlt : |(Q x₀).coeff j| < |(Q x₀).coeff j| + 1 := by linarith
    filter_upwards
      [(hcont j).abs.continuousAt.eventually_mem (isOpen_Iio.mem_nhds hlt)] with x hx
    have hle : |(Q x₀).coeff j| + 1 ≤ ∑ j' ∈ Finset.range (d + 1), (|(Q x₀).coeff j'| + 1) :=
      Finset.single_le_sum (f := fun j' => |(Q x₀).coeff j'| + 1) (fun i _ => by positivity) hj
    have hx' : |(Q x).coeff j| < |(Q x₀).coeff j| + 1 := hx
    linarith
  refine ⟨_, Filter.inter_mem (Filter.inter_mem hdeg hevε) hevC,
    |(Q x₀).coeff d| / 2, hεpos, _, hCnn, ?_⟩
  intro x hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

/-- For a family of real polynomials whose coefficients depend continuously on the parameter and
whose degree is locally constant, the sign of the value at a large argument is the sign of the
leading coefficient: uniformly near a base point `x₀`, with `d` the (local) degree. -/
theorem sign_eval_abs_large {X : Type*} [TopologicalSpace X] (Q : X → Polynomial ℝ)
    (hcont : ∀ j, Continuous fun x => (Q x).coeff j) {x₀ : X} {d : ℕ}
    (hdeg : Filter.Eventually (fun x => (Q x).natDegree = d) (nhds x₀)) :
    ∃ R > 0, Filter.Eventually (fun x => ∀ y : ℝ, R ≤ |y| →
      SignType.sign ((Q x).eval y) = SignType.sign ((Q x).coeff d) * SignType.sign y ^ d)
      (nhds x₀) := by
  rcases d with _ | d'
  · -- degree `0`: the polynomial is the constant `coeff 0`, whatever the argument
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [hdeg] with x hx
    intro y _
    have hev : (Q x).eval y = (Q x).coeff 0 := by
      have h := Polynomial.eval_eq_sum_range (p := Q x) y
      rw [hx] at h
      simpa using h
    rw [hev, pow_zero, mul_one]
  · -- degree `d' + 1 ≥ 1`: on a neighbourhood the leading coefficient stays away from `0` and
    -- the lower coefficients stay bounded, so the leading term dominates for `|y|` beyond a
    -- threshold that is uniform in `x`.
    obtain ⟨W, hW, ε, hεpos, C, hC, hWb⟩ :=
      nhds_coeff_bounds_local Q hcont (d := d' + 1) le_add_self (by simpa using hdeg)
    refine ⟨max 1 (2 * ((d' + 1 : ℕ) : ℝ) * C / ε),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    refine Filter.mem_of_superset hW ?_
    intro x hx y hy
    exact sign_eval_of_coeff_bound le_add_self (hWb x hx).1 hC hεpos (hWb x hx).2.2 (hWb x hx).2.1 hy

end Work.WilE4.CAD
