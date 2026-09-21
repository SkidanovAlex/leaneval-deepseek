import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos
import Submission.Work.Analysis.Abel.integral_moving_split_local
import Submission.Work.Analysis.Calculus.contDiff_dslope

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-!
# The odd first-moment row identity

Proof of `Work.OddVolterra.RowIdentity.odd_rowF`, following Ryabogin's derivation:
the `(n+1)`-st derivative of `momentF` is the sum of

* the `(n+1)`-st derivative of the integral over the *fixed* interval `(-X₁,X₁)`, which is `E1`,
  obtained by differentiating under the integral sign (`window_iteratedDeriv_of_eventually_pos`);
* the `(n+1)`-st derivative of the integral over the *moving* part of the section, which after the
  substitution `t = y σ` / `t = -x σ` becomes a swept integral `∫_u^1 (σ-u)^{n+1/2} B(u,σ) dσ`
  whose derivative is computed by `swept_iteratedDeriv_rpow` and identified with the Abel kernel
  `Kvec` by `kvec_zero_div_sqrt_eq` / `yend_iteratedDeriv_eq_rpow`.
-/

/-- The `y`-endpoint factor of the frozen radicand: `ψ(u,yσ) = (σ-u)·Qy(u,σ)`. -/
def Qy (h y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))

/-- The `-x`-endpoint factor of the frozen radicand: `ψ(u,-xσ) = (σ-u)·Qx(u,σ)`. -/
def Qx (h x : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (-(x σ) + hquot h u σ) * (line h σ (-(x σ)) + line h u (-(x σ)))

/-- The globally smooth auxiliary radicand: `1 - t² - (ut + h u)²`, which agrees with
`psi h semicircle u t` for `|t| ≤ 1`. -/
def Psi (h : ℝ → ℝ) (u t : ℝ) : ℝ := 1 - t ^ 2 - (u * t + h u) ^ 2

/-- The integrand of the swept integral `W`. -/
def Wint (n : ℕ) (h x y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (σ - u) ^ ((n : ℝ) + 1 / 2) *
    ((Qy h y u σ) ^ ((n : ℝ) + 1 / 2) * (-(deriv y σ))
      + (Qx h x u σ) ^ ((n : ℝ) + 1 / 2) * (-(deriv x σ)))

/-- The swept integral. -/
def WW (n : ℕ) (h x y : ℝ → ℝ) (u : ℝ) : ℝ := ∫ σ in u..1, Wint n h x y u σ

/-- The integral over the fixed interval `(-X₁,X₁)`, with the semicircle radicand. -/
def AA (n : ℕ) (h : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in (-(profileX 1))..(profileX 1), (Psi h u t) ^ n * Real.sqrt (Psi h u t)

/-- The data of the odd row identity, packaged. -/
structure Setup where
  n : ℕ
  hn : 1 ≤ n
  a : ℝ
  c : ℝ
  ha : 0 < a
  hac : a ≤ c
  hc1 : c < 1
  h : ℝ → ℝ
  x : ℝ → ℝ
  y : ℝ → ℝ
  f : ℝ → ℝ
  hh : ContDiff ℝ (⊤ : ℕ∞) h
  hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)
  hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0)
  hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1)
  hxy : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
    f (y u) = u * y u + h u ∧ f (-(x u)) = -(u * (-(x u)) + h u)
  hxdec : ∀ σ ∈ Set.Ioo a 1, deriv x σ ≤ 0
  hydec : ∀ σ ∈ Set.Ioo a 1, deriv y σ ≤ 0
  hxb : x 1 = profileX 1
  hyb : y 1 = profileX 1
  hfb : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), f t = semicircle t
  hxle : ∀ s ∈ Set.Icc a 1, x 1 ≤ x s
  hyle : ∀ s ∈ Set.Icc a 1, y 1 ≤ y s
  hord : -x 1 ≤ y 1
  hint : ∀ s ∈ Set.Icc a 1, -(x s) ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1
  hKden : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
    0 < Qy h y s σ ∧ 0 < Qx h x s σ
  hmid : ∀ s ∈ Set.Icc a 1, ∀ t ∈ Set.Ioo (-(profileX 1)) (profileX 1),
    0 < psi h semicircle s t

lemma profileX_one_pos : 0 < profileX 1 := by
  unfold profileX
  positivity

lemma profileX_one_sq : (profileX 1) ^ 2 = 1 / 2 := by
  rw [Commons.Geometry.Ulam.profileX_sq]
  norm_num

lemma profileX_one_le_one : profileX 1 ≤ 1 := by
  have h := profileX_one_sq
  nlinarith [profileX_one_pos]

lemma profileX_one_mem_Icc : profileX 1 ∈ Set.Icc (-(profileX 1)) (profileX 1) :=
  ⟨by linarith [profileX_one_pos], le_rfl⟩

lemma profileX_one_mem_Icc' : profileX 1 ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith [profileX_one_pos], profileX_one_le_one⟩

lemma neg_profileX_one_mem_Icc' : -(profileX 1) ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith [profileX_one_le_one], by linarith [profileX_one_pos]⟩

lemma semicircle_profileX_one : semicircle (profileX 1) = profileX 1 := by
  have hsq : (semicircle (profileX 1)) ^ 2 = (profileX 1) ^ 2 := by
    simpa using Commons.Geometry.Ulam.semicircle_profileX_sq 1
  have hle : 0 ≤ semicircle (profileX 1) := Real.sqrt_nonneg _
  nlinarith [hsq, profileX_one_pos, hle, sq_nonneg (semicircle (profileX 1)),
    sq_nonneg (profileX 1)]

namespace Setup

variable (H : Setup)

lemma h_one : H.h 1 = 0 := by
  have h1 := (H.hxy 1 ⟨by norm_num, le_rfl⟩).1
  rw [H.hyb, H.hfb (profileX 1) profileX_one_mem_Icc, semicircle_profileX_one] at h1
  linarith [h1]

lemma hquot_one {s : ℝ} (hs1 : s ≠ 1) : hquot H.h s 1 = -(1 - s)⁻¹ * H.h s := by
  have hq : H.h 1 - H.h s = (1 - s) * hquot H.h s 1 :=
    sub_mul_hquot (H.hh.of_le (by norm_num)) s 1
  rw [H.h_one] at hq
  have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have : hquot H.h s 1 = -(H.h s) / (1 - s) := by
    rw [eq_div_iff hne]; linarith [hq]
  rw [this]; ring

end Setup

/-- For `|t| ≤ 1`, the semicircle radicand `psi h semicircle u t` is `Psi h u t`. -/
lemma Psi_eq_psi_semicircle (h : ℝ → ℝ) {u t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    psi h semicircle u t = Psi h u t := by
  unfold psi Psi line
  rw [Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc ht]

/-- `Psi h u ·` is a downward parabola, so its value at an interior point is at least the
minimum of its values at the two endpoints `±profileX 1`. -/
lemma Psi_min_le (h : ℝ → ℝ) (u t : ℝ) (ht : t ∈ Set.Icc (-(profileX 1)) (profileX 1)) :
    min (Psi h u (-(profileX 1))) (Psi h u (profileX 1)) ≤ Psi h u t := by
  have hA : 0 < profileX 1 := profileX_one_pos
  have ht' : -(profileX 1) ≤ t ∧ t ≤ profileX 1 := ht
  have hAt : 0 ≤ (profileX 1) ^ 2 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
  have hexp1 : Psi h u (-(profileX 1)) = 1 - (profileX 1) ^ 2 - (-u * profileX 1 + h u) ^ 2 := by
    rw [Psi]; ring
  have hexp2 : Psi h u (profileX 1) = 1 - (profileX 1) ^ 2 - (u * profileX 1 + h u) ^ 2 := by
    rw [Psi]
  have hexp3 : Psi h u t = 1 - t ^ 2 - (u * t + h u) ^ 2 := by rw [Psi]
  have hkey : (profileX 1 - t) * Psi h u (-(profileX 1))
      + (profileX 1 + t) * Psi h u (profileX 1) ≤ Psi h u t * (2 * profileX 1) := by
    rw [hexp1, hexp2, hexp3]
    nlinarith [hAt, mul_nonneg (by positivity : (0:ℝ) ≤ 1 + u ^ 2) hAt, hA,
      sq_nonneg (u * profileX 1 - h u), sq_nonneg (u * profileX 1 + h u),
      sq_nonneg (u * t + h u), sq_nonneg (profileX 1 + t), sq_nonneg (profileX 1 - t)]
  have h2A : (0 : ℝ) < 2 * profileX 1 := by positivity
  have hlam0 : 0 ≤ (profileX 1 - t) / (2 * profileX 1) := by
    apply div_nonneg <;> linarith
  have hlam1 : (profileX 1 - t) / (2 * profileX 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hconv : (profileX 1 - t) / (2 * profileX 1) * Psi h u (-(profileX 1))
      + (1 - (profileX 1 - t) / (2 * profileX 1)) * Psi h u (profileX 1) ≤ Psi h u t := by
    have hid : (profileX 1 - t) / (2 * profileX 1) * Psi h u (-(profileX 1))
        + (1 - (profileX 1 - t) / (2 * profileX 1)) * Psi h u (profileX 1)
        = ((profileX 1 - t) * Psi h u (-(profileX 1))
            + (profileX 1 + t) * Psi h u (profileX 1)) / (2 * profileX 1) := by
      field_simp; ring
    rw [hid, div_le_iff₀ h2A]
    linarith [hkey]
  have hmin : min (Psi h u (-(profileX 1))) (Psi h u (profileX 1))
      ≤ (profileX 1 - t) / (2 * profileX 1) * Psi h u (-(profileX 1))
        + (1 - (profileX 1 - t) / (2 * profileX 1)) * Psi h u (profileX 1) := by
    rcases min_cases (Psi h u (-(profileX 1))) (Psi h u (profileX 1)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      nlinarith [hlam0, hlam1]
    · rw [he]
      nlinarith [hlam0, hlam1]
  exact le_trans hmin hconv

namespace Setup

variable (H : Setup)

/-- `Psi` at the upper endpoint `profileX 1` is nonnegative, as the limit of positive values
inside the interval (`hmid`). -/
lemma Psi_upper_nonneg {s : ℝ} (hs : s ∈ Set.Icc H.a 1) : 0 ≤ Psi H.h s (profileX 1) := by
  have hcont : Continuous fun t : ℝ => Psi H.h s t := by
    have : (fun t : ℝ => Psi H.h s t) = fun t => 1 - t ^ 2 - (s * t + H.h s) ^ 2 := by
      funext t; rw [Psi]
    rw [this]; fun_prop
  have htend : Tendsto (fun t : ℝ => Psi H.h s t) (𝓝[<] (profileX 1))
      (𝓝 (Psi H.h s (profileX 1))) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT (by linarith [profileX_one_pos] :
    -(profileX 1) < profileX 1)] with t ht
  rw [← Psi_eq_psi_semicircle H.h (u := s) ?_]
  · exact le_of_lt (H.hmid s hs t ht)
  · exact ⟨by linarith [profileX_one_le_one, ht.1], by linarith [profileX_one_le_one, ht.2]⟩

/-- `Psi` at the lower endpoint `-profileX 1` is nonnegative. -/
lemma Psi_lower_nonneg {s : ℝ} (hs : s ∈ Set.Icc H.a 1) :
    0 ≤ Psi H.h s (-(profileX 1)) := by
  have hcont : Continuous fun t : ℝ => Psi H.h s t := by
    have : (fun t : ℝ => Psi H.h s t) = fun t => 1 - t ^ 2 - (s * t + H.h s) ^ 2 := by
      funext t; rw [Psi]
    rw [this]; fun_prop
  have htend : Tendsto (fun t : ℝ => Psi H.h s t) (𝓝[>] (-(profileX 1)))
      (𝓝 (Psi H.h s (-(profileX 1)))) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith [profileX_one_pos] :
    -(profileX 1) < profileX 1)] with t ht
  rw [← Psi_eq_psi_semicircle H.h (u := s) ?_]
  · exact le_of_lt (H.hmid s hs t ht)
  · exact ⟨by linarith [profileX_one_le_one, ht.1], by linarith [profileX_one_le_one, ht.2]⟩

/-- At the upper endpoint, `Psi` is strictly positive: the vanishing case is excluded by the
positivity hypothesis `hKden` for the frozen `y`-factor. -/
lemma Psi_upper_pos {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) : 0 < Psi H.h s (profileX 1) := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; linarith [hs.2, H.hc1]
  have hsIcc : s ∈ Set.Icc H.a 1 := ⟨hs.1, le_trans hs.2 H.hc1.le⟩
  refine lt_of_le_of_ne' (Psi_upper_nonneg H hsIcc) (fun hzero => ?_)
  rw [eq_comm] at hzero
  have hsq : (s * profileX 1 + H.h s) ^ 2 = (profileX 1) ^ 2 := by
    have h := hzero; rw [Psi] at h
    linarith [h, profileX_one_sq]
  have hK1 := (H.hKden s 1 hs.1 hsIcc.2 le_rfl).1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hc | hc
  · have hquot : hquot H.h s 1 = -profileX 1 := by
      have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
      have hval : H.h s = profileX 1 * (1 - s) := by linarith [hc]
      rw [H.hquot_one hs1, hval]
      field_simp
    have hzeroQ : Qy H.h H.y s 1 = 0 := by
      unfold Qy
      rw [H.hyb, hquot]
      ring
    rw [hzeroQ] at hK1
    exact lt_irrefl 0 hK1
  · have hzeroQ : Qy H.h H.y s 1 = 0 := by
      unfold Qy
      have hlin : line H.h 1 (H.y 1) + line H.h s (H.y 1) = 0 := by
        simp only [line]
        rw [H.hyb, H.h_one]
        linarith [hc]
      rw [hlin, mul_zero]
    rw [hzeroQ] at hK1
    exact lt_irrefl 0 hK1

/-- At the lower endpoint, `Psi` is strictly positive: the vanishing case is excluded by the
positivity hypothesis `hKden` for the frozen `-x`-factor. -/
lemma Psi_lower_pos {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) : 0 < Psi H.h s (-(profileX 1)) := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; linarith [hs.2, H.hc1]
  have hsIcc : s ∈ Set.Icc H.a 1 := ⟨hs.1, le_trans hs.2 H.hc1.le⟩
  refine lt_of_le_of_ne' (Psi_lower_nonneg H hsIcc) (fun hzero => ?_)
  rw [eq_comm] at hzero
  have hsq : (H.h s - s * profileX 1) ^ 2 = (profileX 1) ^ 2 := by
    have h := hzero; rw [Psi] at h
    linarith [h, profileX_one_sq]
  have hK2 := (H.hKden s 1 hs.1 hsIcc.2 le_rfl).2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hc | hc
  · have hzeroQ : Qx H.h H.x s 1 = 0 := by
      unfold Qx
      have hlin : line H.h 1 (-(H.x 1)) + line H.h s (-(H.x 1)) = 0 := by
        simp only [line]
        rw [H.hxb, H.h_one]
        linarith [hc]
      rw [hlin, mul_zero]
    rw [hzeroQ] at hK2
    exact lt_irrefl 0 hK2
  · have hquot : hquot H.h s 1 = profileX 1 := by
      have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
      have hval : H.h s = -(profileX 1) * (1 - s) := by linarith [hc]
      rw [H.hquot_one hs1, hval]
      field_simp
    have hzeroQ : Qx H.h H.x s 1 = 0 := by
      unfold Qx
      rw [H.hxb, hquot]
      ring
    rw [hzeroQ] at hK2
    exact lt_irrefl 0 hK2

/-- Positivity of `Psi` on a two-sided window of slopes around `s` and the whole section
`[-profileX 1, profileX 1]`.  On a neighbourhood of `s` this follows from positivity at the two
endpoints and the concavity of the parabola `Psi h u ·`. -/
lemma Psi_window_pos {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) :
    ∃ ε > 0, ∀ u : ℝ, |u - s| < ε →
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < Psi H.h u t := by
  have hhcont : Continuous H.h := H.hh.continuous
  have hcont1 : Continuous fun u : ℝ => Psi H.h u (profileX 1) := by
    have : (fun u : ℝ => Psi H.h u (profileX 1))
        = fun u => 1 - (profileX 1) ^ 2 - (u * profileX 1 + H.h u) ^ 2 := by
      funext u; rw [Psi]
    rw [this]; fun_prop
  have hcont2 : Continuous fun u : ℝ => Psi H.h u (-(profileX 1)) := by
    have : (fun u : ℝ => Psi H.h u (-(profileX 1)))
        = fun u => 1 - (-(profileX 1)) ^ 2 - (u * (-(profileX 1)) + H.h u) ^ 2 := by
      funext u; rw [Psi]
    rw [this]; fun_prop
  obtain ⟨ε1, hε1, hε1'⟩ : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → 0 < Psi H.h u (profileX 1) := by
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp
      (hcont1.continuousAt.eventually (isOpen_Ioi.mem_nhds (Psi_upper_pos H hs)))
    exact ⟨ε, hε, fun u hu => hb (by simpa [Metric.mem_ball, Real.dist_eq] using hu)⟩
  obtain ⟨ε2, hε2, hε2'⟩ : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → 0 < Psi H.h u (-(profileX 1)) := by
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp
      (hcont2.continuousAt.eventually (isOpen_Ioi.mem_nhds (Psi_lower_pos H hs)))
    exact ⟨ε, hε, fun u hu => hb (by simpa [Metric.mem_ball, Real.dist_eq] using hu)⟩
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun u hu t ht => ?_⟩
  have hu1 : |u - s| < ε1 := lt_of_lt_of_le hu (min_le_left _ _)
  have hu2 : |u - s| < ε2 := lt_of_lt_of_le hu (min_le_right _ _)
  exact lt_of_lt_of_le (lt_min (hε2' u hu2) (hε1' u hu1)) (Psi_min_le H.h u t ht)

end Setup
