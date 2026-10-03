import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.RingTheory.SimpleRing.Principal

open Complex Metric

namespace Commons.Analysis.Complex.Koebe

/-- **Landau implies a weak Koebe (one-quarter) inequality.**  Fix `c₀ > 0` and assume the Landau
property: every function holomorphic on the unit disc with `f 0 = 0`, `deriv f 0 = 1` has an image
containing a disc of radius `c₀`.  Then every univalent `f` on the unit disc with `f 0 = 0`,
`deriv f 0 = 1` omits no value of modulus `< c₀/π`.

Proof route (all elementary):
* for an omitted value `w` define `G z = w * f z / (w - f z)`; then `G` is univalent on the disc,
  `G 0 = 0`, `deriv G 0 = 1` and `G` omits `-w`;
* `H z = 1 + G z / w` is holomorphic and nowhere zero on the disc.  Since the disc is a ball, a
  primitive of `deriv H / H` exists (`DifferentiableOn.isExactOn_ball`), giving a holomorphic `L`
  with `exp ∘ L = H` and `L 0 = 0` (adjust by `2πiℤ`), so `deriv L 0 = 1/w`;
* if `L z₁ - L z₂ ∈ 2πiℤ \ {0}` then `H z₁ = H z₂`, hence `G z₁ = G z₂`, hence `z₁ = z₂`; thus the
  image of `w * L` contains no two points whose difference is a nonzero element of `2πiwℤ`;
* the Landau hypothesis applies to `w * L` (`(w*L) 0 = 0`, `deriv (w*L) 0 = 1`) and yields a disc
  of radius `c₀` inside its image.  If `π ‖w‖ ≤ c₀`, the two points `w₀ ± πiw` of that disc differ
  by the forbidden value `2πiw`, a contradiction.  Hence `π‖w‖ > c₀`. -/
theorem weak_koebe_of_landau {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlandau : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) → f 0 = 0 →
      deriv f 0 = 1 → ∃ w : ℂ, Metric.closedBall w c₀ ⊆ f '' (Metric.ball (0 : ℂ) 1)) :
    ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ w : ℂ, w ∉ f '' (Metric.ball (0 : ℂ) 1) → c₀ / Real.pi ≤ ‖w‖ := by
  intro f hf hinj hf0 hf1 w hw
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  -- the omitted value is nonzero
  have hw0 : w ≠ 0 := by
    intro h
    exact hw ⟨0, h0mem, by rw [hf0, h]⟩
  -- the denominator never vanishes on the disc
  have hden : ∀ z ∈ Metric.ball (0 : ℂ) 1, w - f z ≠ 0 := by
    intro z hz h
    exact hw ⟨z, hz, (sub_eq_zero.mp h).symm⟩
  -- differentiability of f and of deriv f on the disc
  have hfd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hf z hz).differentiableAt.differentiableWithinAt
  have hdfd : DifferentiableOn ℂ (deriv f) (Metric.ball (0 : ℂ) 1) :=
    hfd.deriv isOpen_ball
  -- the logarithmic derivative f'/(w - f) of H = w/(w - f)
  have hφd : DifferentiableOn ℂ (fun z => deriv f z / (w - f z)) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hdfd z hz).div ((hfd z hz).const_sub w) (hden z hz)
  -- a primitive L of it, normalised by L 0 = 0
  obtain ⟨L, hL0, hL⟩ := hφd.isExactOn_ball.with_val_at 0 0
  -- the function `exp (L ·) * (w - f ·)` is constant, equal to w
  have hPderiv : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun y => Complex.exp (L y) * (w - f y)) 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun y => Complex.exp (L y))
        (Complex.exp (L z) * (deriv f z / (w - f z))) z := (hL z hz).cexp
    have h2 : HasDerivAt (fun y => w - f y) (-(deriv f z)) z :=
      ((hf z hz).differentiableAt.hasDerivAt).const_sub w
    have h3 : HasDerivAt (fun y => Complex.exp (L y) * (w - f y))
        (Complex.exp (L z) * (deriv f z / (w - f z)) * (w - f z)
          + Complex.exp (L z) * (-(deriv f z))) z := (h1.mul h2)
    have hv : Complex.exp (L z) * (deriv f z / (w - f z)) * (w - f z)
        + Complex.exp (L z) * (-(deriv f z)) = 0 := by
      rw [mul_assoc, div_mul_cancel₀ _ (hden z hz)]
      ring
    rw [hv] at h3
    exact h3
  have hPdiff : DifferentiableOn ℂ (fun y => Complex.exp (L y) * (w - f y))
      (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hPderiv z hz).differentiableAt.differentiableWithinAt
  have hPconst : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (L z) * (w - f z) = w := by
    intro z hz
    have heq : Set.EqOn (deriv (fun y => Complex.exp (L y) * (w - f y))) 0
        (Metric.ball (0 : ℂ) 1) := by
      intro y hy
      simp [(hPderiv y hy).deriv]
    have hcz : Complex.exp (L z) * (w - f z) = Complex.exp (L 0) * (w - f 0) :=
      IsOpen.is_const_of_deriv_eq_zero isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
        hPdiff heq hz h0mem
    rw [hcz]
    simp [hL0, hf0]
  -- hence exp ∘ L = H on the disc
  have hH : ∀ z ∈ Metric.ball (0 : ℂ) 1, Complex.exp (L z) = w / (w - f z) :=
    fun z hz => (eq_div_iff (hden z hz)).mpr (hPconst z hz)
  -- Landau's hypothesis applied to w * L
  have hgdiff : DifferentiableOn ℂ (fun z => w * L z) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hL z hz).differentiableAt.const_mul w |>.differentiableWithinAt
  have hg0 : (fun z => w * L z) 0 = 0 := by simp [hL0]
  have hg1 : deriv (fun z => w * L z) 0 = 1 := by
    have hd : deriv L 0 = deriv f 0 / (w - f 0) := (hL 0 h0mem).deriv
    rw [deriv_const_mul w ((hL 0 h0mem).differentiableAt), hd, hf0, hf1, sub_zero, one_div,
      mul_inv_cancel₀ hw0]
  obtain ⟨w₀, hw₀⟩ := hlandau (fun z => w * L z)
    (fun z hz => hgdiff.analyticAt (isOpen_ball.mem_nhds hz)) hg0 hg1
  -- no two points of the disc have images under L differing by a nonzero multiple of 2πi
  have hforbid : ∀ z₁ ∈ Metric.ball (0 : ℂ) 1, ∀ z₂ ∈ Metric.ball (0 : ℂ) 1, ∀ m : ℤ,
      L z₁ - L z₂ = (m : ℂ) * (2 * ↑Real.pi * I) → m = 0 := by
    intro z₁ hz₁ z₂ hz₂ m hm
    have hexp : Complex.exp (L z₁) = Complex.exp (L z₂) := by
      have h1 : L z₁ = L z₂ + (m : ℂ) * (2 * ↑Real.pi * I) := by rw [← hm]; ring
      rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hfeq : f z₁ = f z₂ := by
      have hH₁ := hH z₁ hz₁
      have hH₂ := hH z₂ hz₂
      rw [hexp] at hH₁
      have hdd : w / (w - f z₁) = w / (w - f z₂) := hH₁.symm.trans hH₂
      rw [div_eq_div_iff (hden z₁ hz₁) (hden z₂ hz₂)] at hdd
      have hcan : w - f z₂ = w - f z₁ := mul_left_cancel₀ hw0 hdd
      exact (sub_right_inj.mp hcan).symm
    have hz : z₁ = z₂ := hinj hz₁ hz₂ hfeq
    rw [hz, sub_self] at hm
    have h2pi : (2 : ℂ) * (↑Real.pi) * I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    rcases mul_eq_zero.mp hm.symm with h | h
    · exact_mod_cast h
    · exact absurd h h2pi
  -- it remains to contradict Landau's disc
  suffices h : ¬ (Real.pi * ‖w‖ ≤ c₀) by
    rw [div_le_iff₀ Real.pi_pos]
    have h1 : c₀ < Real.pi * ‖w‖ := not_le.mp h
    have h2 : Real.pi * ‖w‖ = ‖w‖ * Real.pi := mul_comm _ _
    linarith
  intro hle
  have hnorm : ‖(↑Real.pi : ℂ) * w * I‖ = Real.pi * ‖w‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hp : w₀ + ↑Real.pi * w * I ∈ Metric.closedBall w₀ c₀ := by
    rw [Metric.mem_closedBall, Complex.dist_eq,
      show w₀ + ↑Real.pi * w * I - w₀ = ↑Real.pi * w * I by ring, hnorm]
    exact hle
  have hq : w₀ - ↑Real.pi * w * I ∈ Metric.closedBall w₀ c₀ := by
    rw [Metric.mem_closedBall, Complex.dist_eq,
      show w₀ - ↑Real.pi * w * I - w₀ = -(↑Real.pi * w * I) by ring, norm_neg, hnorm]
    exact hle
  obtain ⟨z₁, hz₁, hz₁eq⟩ := hw₀ hp
  obtain ⟨z₂, hz₂, hz₂eq⟩ := hw₀ hq
  have hz₁eq' : w * L z₁ = w₀ + ↑Real.pi * w * I := hz₁eq
  have hz₂eq' : w * L z₂ = w₀ - ↑Real.pi * w * I := hz₂eq
  have hLdiff : L z₁ - L z₂ = (2 : ℂ) * ↑Real.pi * I := by
    have hmul : w * (L z₁ - L z₂) = (2 : ℂ) * ↑Real.pi * I * w := by
      have hsub : w * L z₁ - w * L z₂ = (2 : ℂ) * ↑Real.pi * I * w := by
        rw [hz₁eq', hz₂eq']
        ring
      rw [← hsub]; ring
    have h2 : w * (L z₁ - L z₂) = w * ((2 : ℂ) * ↑Real.pi * I) := by rw [hmul]; ring
    exact mul_left_cancel₀ hw0 h2
  have hm1 : L z₁ - L z₂ = ((1 : ℤ) : ℂ) * (2 * ↑Real.pi * I) := by
    rw [hLdiff]; push_cast; ring
  exact one_ne_zero (hforbid z₁ hz₁ z₂ hz₂ 1 hm1)

end Commons.Analysis.Complex.Koebe