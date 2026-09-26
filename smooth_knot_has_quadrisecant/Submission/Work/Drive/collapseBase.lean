import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.uniformCurveBounds
import Submission.Work.Drive.spatial_le_slope_mul_dist
import Submission.Work.Drive.knot_tangent_chord_bound
import Submission.Helpers

set_option maxHeartbeats 1000000

/-!
# A self-contained copy of the geometric bounds used by the collapse-resistance proof

This module re-states (and re-proves, from the same sources) the three analytic inputs of
`Work.Drive.collapseResistance`, so that the collapse-resistance development does not depend on the
`sweep`-side modules:

* `Work.Drive.speedLowerBound` — a uniform positive lower bound for the speed of a smooth knot;
* `Work.Drive.knotC2Bounds` — uniform bounds for the speed, the velocity-Lipschitz constant of a
  smooth knot (a copy of `Work.Drive.exists_knot_c2_bounds`);
* `Work.Drive.lipOfDerivBound` — a derivative bound gives a Lipschitz bound;
* `Work.Drive.baseWindowStrict` — the base-map window with strict anti-monotonicity (a copy of
  `Work.Drive.baseMapWindowStrict`, with the same proof);
* `Work.Drive.baseWindow` — the `IsSmoothKnot` wrapper of the window statement.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

noncomputable section

/-- **Uniform lower bound for the speed.** -/
theorem speedLowerBound {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c ≤ ‖velocity r t‖ := by
  have hcont : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hper : Function.Periodic (velocity r) period := fun t => hr.velocity_periodic t
  obtain ⟨t0, _ht0, hmin⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := period)).exists_isMinOn
      ⟨0, Set.mem_Icc.mpr ⟨le_rfl, period_pos.le⟩⟩ hcont.norm.continuousOn
  refine ⟨‖velocity r t0‖, norm_pos_iff.mpr (hr.regular t0), ?_⟩
  intro t
  have h1 : ‖velocity r t‖ = ‖velocity r (resid t)‖ := by
    rw [resid]
    exact congrArg Norm.norm ((hper.int_mul ⌊t / period⌋).sub_eq t).symm
  rw [h1]
  exact hmin ⟨(resid_mem t).1, (resid_mem t).2.le⟩

theorem knotC2Bounds {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ m M C : ℝ, 0 < m ∧ 0 < M ∧ 0 < C ∧
      (∀ t : ℝ, m ≤ ‖velocity r t‖) ∧ (∀ t : ℝ, ‖velocity r t‖ ≤ M) ∧
      (∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|) := by
  have hp : 0 < period := period_pos
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hvper : Function.Periodic (velocity r) period := by
    intro t
    have h1 : (fun y : ℝ => r (y + period)) = r := funext fun y => hr.periodic y
    have h2 : deriv (fun y : ℝ => r (y + period)) t = deriv r (t + period) :=
      deriv_comp_add_const r period t
    rw [h1] at h2
    exact h2.symm
  have hne : (Set.Icc (0 : ℝ) period).Nonempty := ⟨0, le_rfl, hp.le⟩
  obtain ⟨t₀, _, hmin₀⟩ := isCompact_Icc.exists_isMinOn hne hvcont.norm.continuousOn
  obtain ⟨t₁, _, hmax₀⟩ := isCompact_Icc.exists_isMaxOn hne hvcont.norm.continuousOn
  have hmpos : 0 < ‖velocity r t₀‖ := norm_pos_iff.mpr (hr.regular t₀)
  have hMpos : 0 < ‖velocity r t₁‖ + 1 := by positivity
  have hderivCin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    exact ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2
  have hd2cont : Continuous (fun t : ℝ => deriv (deriv r) t) :=
    hderivCin.continuous_deriv (by simp)
  have hd2per : Function.Periodic (fun t : ℝ => deriv (deriv r) t) period := by
    intro t
    have h1 : (fun y : ℝ => deriv r (y + period)) = deriv r := funext fun y => hvper y
    have h2 : deriv (fun y : ℝ => deriv r (y + period)) t = deriv (deriv r) (t + period) :=
      deriv_comp_add_const (deriv r) period t
    rw [h1] at h2
    exact h2.symm
  obtain ⟨t₂, _, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hd2cont.norm.continuousOn
  set C : ℝ := ‖deriv (deriv r) t₂‖ + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCbound : ∀ t : ℝ, ‖deriv (deriv r) t‖ ≤ C := by
    intro t
    obtain ⟨y, hy, hty⟩ := hd2per.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖deriv (deriv r) t‖ = ‖deriv (deriv r) y‖ := by rw [hty]
      _ ≤ ‖deriv (deriv r) t₂‖ := hmax₂ hy'
      _ ≤ C := by rw [hCdef]; linarith
  have hveldiff : Differentiable ℝ (velocity r) := hderivCin.differentiable (by simp)
  have hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t| := by
    intro t t'
    rcases le_total t t' with hle | hle
    · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := velocity r)
        (f' := fun x : ℝ => deriv (deriv r) x) (a := t) (b := t') (C := C)
        (fun x _ => (hveldiff x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hCbound x) t' ⟨hle, le_rfl⟩
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t' - t), norm_sub_rev]
      exact h
    · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := velocity r)
        (f' := fun x : ℝ => deriv (deriv r) x) (a := t') (b := t) (C := C)
        (fun x _ => (hveldiff x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hCbound x) t ⟨hle, le_rfl⟩
      rw [abs_of_nonpos (by linarith : t' - t ≤ 0), neg_sub]
      exact h
  refine ⟨‖velocity r t₀‖, ‖velocity r t₁‖ + 1, C, hmpos, hMpos, hCpos, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖velocity r t₀‖ ≤ ‖velocity r y‖ := hmin₀ hy'
      _ = ‖velocity r t‖ := by rw [hty]
  · intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖velocity r t‖ = ‖velocity r y‖ := by rw [hty]
      _ ≤ ‖velocity r t₁‖ := hmax₀ hy'
      _ ≤ ‖velocity r t₁‖ + 1 := by linarith
  · exact hlip


lemma lipOfDerivBound {f : ℝ → Space} {C : ℝ}
    (hdiff : ∀ t : ℝ, HasDerivAt f (deriv f t) t) (hC : ∀ t : ℝ, ‖deriv f t‖ ≤ C) :
    ∀ x y : ℝ, ‖f y - f x‖ ≤ C * |y - x| := by
  have hone : ∀ x y : ℝ, x ≤ y → ‖f y - f x‖ ≤ C * (y - x) := by
    intro x y hxy
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (s := Set.Icc x y)
      (x := x) (y := y) (C := C) (fun u _ => (hdiff u).differentiableAt) (fun u _ => hC u)
      (convex_Icc x y) ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hmvt
  intro x y
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    exact hone x y hxy
  · rw [abs_of_nonpos (by linarith : y - x ≤ 0), neg_sub]
    rw [norm_sub_rev]
    exact hone y x hxy

theorem baseWindowStrict {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} {vhi A c δ : ℝ}
    (hvhi : 0 < vhi) (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ)
    (hspd : ∀ t : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r t‖ ≤ vhi)
    (hvlip : ∀ x y : ℝ, ‖LeanEval.KnotTheory.Quadrisecant.velocity r y -
      LeanEval.KnotTheory.Quadrisecant.velocity r x‖ ≤ A * |y - x|)
    (hrlip : ∀ x y : ℝ, ‖r y - r x‖ ≤ vhi * |y - x|)
    (hchord : ∀ y z : ℝ, y < z → z - y ≤ δ →
      c * (z - y) ≤ inner ℝ (LeanEval.KnotTheory.Quadrisecant.velocity r y) (r z - r y))
    (hcont : ∀ q : LeanEval.KnotTheory.Quadrisecant.Space, Continuous fun t : ℝ =>
      inner ℝ (q - r t) (LeanEval.KnotTheory.Quadrisecant.velocity r t)) :
    ∃ T N κ ηb : ℝ, 0 < T ∧ 0 < N ∧ 0 < κ ∧ 0 < ηb ∧
      ∀ c₀ : ℝ, ∀ Θ : ℝ, 0 < Θ → Θ ≤ ηb → ∀ t₀ : ℝ, |t₀ - c₀| ≤ T / 4 →
      ∀ q : LeanEval.KnotTheory.Quadrisecant.Space,
        ‖q - r t₀‖ ≤ Θ →
        ∃ x : ℝ, (x ∈ Set.Ioo (c₀ - T) (c₀ + T) ∧
            inner ℝ (q - r x) (LeanEval.KnotTheory.Quadrisecant.velocity r x) = 0 ∧
            |x - t₀| ≤ N * Θ ∧ ‖q - r x‖ ≤ κ * Θ) ∧
          (∀ y : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) →
            inner ℝ (q - r y) (LeanEval.KnotTheory.Quadrisecant.velocity r y) = 0 → y = x) ∧
          (∀ y z : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) → z ∈ Set.Ioo (c₀ - T) (c₀ + T) →
            y < z → inner ℝ (q - r z) (LeanEval.KnotTheory.Quadrisecant.velocity r z) <
              inner ℝ (q - r y) (LeanEval.KnotTheory.Quadrisecant.velocity r y)) := by
  set T : ℝ := min (δ / 2)
    (min 1 (min (c / (64 * (A + 1))) (c / (64 * (A * vhi + 1))))) with hT
  set N : ℝ := 4 * vhi / c with hN
  set κ : ℝ := 1 + vhi * N with hκ
  set ηb : ℝ := min (T / 4) (T * (c / (32 * vhi))) with hηb
  have hTpos : 0 < T := by
    rw [hT]
    exact lt_min (by linarith) (lt_min one_pos
      (lt_min (div_pos hc (by positivity)) (div_pos hc (by positivity))))
  have hTle1 : T ≤ c / (64 * (A + 1)) := by
    rw [hT]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTle2 : T ≤ c / (64 * (A * vhi + 1)) := by
    rw [hT]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hTδ : 2 * T ≤ δ := by
    rw [hT]
    have h := min_le_left (δ / 2) (min 1 (min (c / (64 * (A + 1))) (c / (64 * (A * vhi + 1)))))
    linarith
  have hNpos : 0 < N := by
    rw [hN]; exact div_pos (by linarith) hc
  have hκpos : 0 < κ := by
    rw [hκ]; nlinarith [hNpos, hvhi]
  have hηbpos : 0 < ηb := by
    rw [hηb]
    exact lt_min (by linarith) (mul_pos hTpos (div_pos hc (by linarith)))
  have hηb1 : ηb ≤ T / 4 := by rw [hηb]; exact min_le_left _ _
  have hηb2 : ηb ≤ T * (c / (32 * vhi)) := by rw [hηb]; exact min_le_right _ _
  have hNηb : N * ηb ≤ T / 4 := by
    have h1 : N * ηb ≤ N * (T * (c / (32 * vhi))) := mul_le_mul_of_nonneg_left hηb2 hNpos.le
    have h2 : N * (T * (c / (32 * vhi))) = T / 8 := by
      rw [hN]
      field_simp
      ring
    linarith
  have hAT : A * T ≤ c / 64 := by
    have h1 : A * T ≤ A * (c / (64 * (A + 1))) := mul_le_mul_of_nonneg_left hTle1 hA
    have h2 : A * (c / (64 * (A + 1))) ≤ c / 64 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (A + 1))]
      nlinarith [hA, hc]
    linarith
  have hATvhi : A * T * vhi ≤ c / 64 := by
    have h1 : A * T * vhi ≤ A * (c / (64 * (A * vhi + 1))) * vhi := by
      have h := mul_le_mul_of_nonneg_left hTle2 hA
      nlinarith [h, hvhi]
    have h2 : A * (c / (64 * (A * vhi + 1))) * vhi ≤ c / 64 := by
      have he : A * (c / (64 * (A * vhi + 1))) * vhi
          = (A * vhi) * c / (64 * (A * vhi + 1)) := by ring
      rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (A * vhi + 1))]
      nlinarith [mul_nonneg hA hvhi.le, hc]
    linarith
  have hkey : A * (ηb + 2 * T * vhi) ≤ c / 2 := by
    have h1 : A * ηb ≤ A * (T / 4) := mul_le_mul_of_nonneg_left hηb1 hA
    have h2 : A * (T / 4) ≤ c / 256 := by nlinarith [hAT]
    have h3 : A * (2 * T * vhi) = 2 * (A * T * vhi) := by ring
    have h4 : 2 * (A * T * vhi) ≤ c / 32 := by linarith [hATvhi]
    have h5 : A * (ηb + 2 * T * vhi) = A * ηb + A * (2 * T * vhi) := by ring
    rw [h5]
    linarith
  refine ⟨T, N, κ, ηb, hTpos, hNpos, hκpos, hηbpos, ?_⟩
  intro c₀ Θ hΘ hΘηb t₀ ht₀ q hq
  set Φ : ℝ → ℝ := fun t => inner ℝ (q - r t) (velocity r t) with hΦ
  have hΦcont : Continuous Φ := by
    rw [hΦ]
    exact hcont q
  have hτ : N * Θ ≤ T / 4 := by
    have h1 : N * Θ ≤ N * ηb := mul_le_mul_of_nonneg_left hΘηb hNpos.le
    linarith
  have hNΘpos : 0 < N * Θ := mul_pos hNpos hΘ
  have ht₀win : t₀ ∈ Set.Ioo (c₀ - T) (c₀ + T) := by
    rw [Set.mem_Ioo]
    have h := abs_le.mp ht₀
    constructor <;> linarith
  -- the window bound on `‖q - r y‖`
  have hwin : ∀ y : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) → ‖q - r y‖ ≤ Θ + 2 * T * vhi := by
    intro y hy
    have h1 : ‖q - r y‖ ≤ ‖q - r t₀‖ + ‖r t₀ - r y‖ := by
      have he : q - r y = (q - r t₀) + (r t₀ - r y) := by abel
      rw [he]; exact norm_add_le _ _
    have h2 : ‖r t₀ - r y‖ ≤ vhi * |t₀ - y| := by
      have h := hrlip t₀ y
      rwa [norm_sub_rev, abs_sub_comm] at h
    have h3 : |t₀ - y| ≤ 2 * T := by
      have hy' : |y - c₀| < T := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have h4 : |t₀ - y| ≤ |t₀ - c₀| + |c₀ - y| := abs_sub_le t₀ c₀ y
      have h5 : |c₀ - y| = |y - c₀| := abs_sub_comm c₀ y
      linarith [ht₀]
    have h6 : vhi * |t₀ - y| ≤ vhi * (2 * T) := mul_le_mul_of_nonneg_left h3 hvhi.le
    calc ‖q - r y‖ ≤ ‖q - r t₀‖ + ‖r t₀ - r y‖ := h1
      _ ≤ Θ + vhi * (2 * T) := by linarith [h2, h6, hq]
      _ = Θ + 2 * T * vhi := by ring
  -- the key estimate
  have hstep : ∀ y z : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) → z ∈ Set.Ioo (c₀ - T) (c₀ + T) →
      y < z → Φ z - Φ y ≤ (z - y) * (A * (Θ + 2 * T * vhi) - c) := by
    intro y z hy hz hyz
    have hzyδ : z - y ≤ δ := by
      have h1 : z - y < 2 * T := by linarith [hy.1, hz.2]
      linarith [hTδ]
    have hqz : ‖q - r z‖ ≤ Θ + 2 * T * vhi := hwin z hz
    have hvz : ‖velocity r z - velocity r y‖ ≤ A * (z - y) := by
      have h := hvlip y z
      rw [abs_of_pos (by linarith : (0 : ℝ) < z - y)] at h
      exact h
    have hch := hchord y z hyz hzyδ
    have hiden : Φ z - Φ y = inner ℝ (q - r z) (velocity r z - velocity r y)
        - inner ℝ (r z - r y) (velocity r y) := by
      have hadd : q - r y = (q - r z) + (r z - r y) := by abel
      rw [hΦ]
      simp only
      rw [hadd, inner_add_left, inner_sub_right]
      ring
    rw [hiden]
    have ht1 : inner ℝ (q - r z) (velocity r z - velocity r y)
        ≤ (z - y) * (A * (Θ + 2 * T * vhi)) := by
      have h1 := real_inner_le_norm (q - r z) (velocity r z - velocity r y)
      have h5 : ‖q - r z‖ * ‖velocity r z - velocity r y‖
          ≤ (Θ + 2 * T * vhi) * (A * (z - y)) :=
        mul_le_mul hqz hvz (norm_nonneg _) (by positivity)
      have h6 : (Θ + 2 * T * vhi) * (A * (z - y))
          = (z - y) * (A * (Θ + 2 * T * vhi)) := by ring
      linarith
    have hch' : c * (z - y) ≤ inner ℝ (r z - r y) (velocity r y) := by
      rw [real_inner_comm]
      exact hch
    have hfin : inner ℝ (q - r z) (velocity r z - velocity r y)
        - inner ℝ (r z - r y) (velocity r y)
        ≤ (z - y) * (A * (Θ + 2 * T * vhi)) - c * (z - y) := by linarith
    have heq : (z - y) * (A * (Θ + 2 * T * vhi)) - c * (z - y)
        = (z - y) * (A * (Θ + 2 * T * vhi) - c) := by ring
    linarith
  have hAt : A * (Θ + 2 * T * vhi) ≤ c / 2 := by
    have h2 : Θ + 2 * T * vhi ≤ ηb + 2 * T * vhi := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left h2 hA) hkey
  have hstrict : ∀ y z : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) → z ∈ Set.Ioo (c₀ - T) (c₀ + T) →
      y < z → Φ z < Φ y := by
    intro y z hy hz hyz
    have h := hstep y z hy hz hyz
    have h1 : A * (Θ + 2 * T * vhi) - c < 0 := by linarith
    have h2 : 0 < z - y := by linarith
    have h3 : (z - y) * (A * (Θ + 2 * T * vhi) - c) < 0 := mul_neg_of_pos_of_neg h2 h1
    linarith
  -- endpoint bounds
  have hΦabs : |Φ t₀| ≤ Θ * vhi := by
    have h1 : |inner ℝ (q - r t₀) (velocity r t₀)| ≤ ‖q - r t₀‖ * ‖velocity r t₀‖ :=
      abs_real_inner_le_norm _ _
    have h2 : ‖q - r t₀‖ * ‖velocity r t₀‖ ≤ Θ * vhi :=
      mul_le_mul hq (hspd t₀) (norm_nonneg _) hΘ.le
    have h3 : Φ t₀ = inner ℝ (q - r t₀) (velocity r t₀) := by rw [hΦ]
    linarith [abs_le.mp (le_trans h1 h2)]
  have hΘvhipos : 0 < Θ * vhi := mul_pos hΘ hvhi
  have hright : Φ (t₀ + N * Θ) < 0 := by
    have hz : t₀ + N * Θ ∈ Set.Ioo (c₀ - T) (c₀ + T) := by
      rw [Set.mem_Ioo]
      have h := abs_le.mp ht₀
      constructor
      · linarith [h.1, hτ, hTpos, hNΘpos.le]
      · linarith [h.2, hτ, hTpos, hNΘpos.le]
    have h := hstep t₀ (t₀ + N * Θ) ht₀win hz (by linarith [hNΘpos])
    have h2 : A * (Θ + 2 * T * vhi) - c ≤ -(c / 2) := by linarith
    have h3 : (N * Θ) * (A * (Θ + 2 * T * vhi) - c) ≤ (N * Θ) * (-(c / 2)) :=
      mul_le_mul_of_nonneg_left h2 hNΘpos.le
    have h4 : (N * Θ) * (c / 2) = 2 * (Θ * vhi) := by
      rw [hN]; field_simp; ring
    have h5 : Φ t₀ ≤ Θ * vhi := (abs_le.mp hΦabs).2
    linarith
  have hleft : 0 < Φ (t₀ - N * Θ) := by
    have hz : t₀ - N * Θ ∈ Set.Ioo (c₀ - T) (c₀ + T) := by
      rw [Set.mem_Ioo]
      have h := abs_le.mp ht₀
      constructor
      · linarith [h.1, hτ, hTpos, hNΘpos.le]
      · linarith [h.2, hτ, hTpos, hNΘpos.le]
    have h := hstep (t₀ - N * Θ) t₀ hz ht₀win (by linarith [hNΘpos])
    have h2 : A * (Θ + 2 * T * vhi) - c ≤ -(c / 2) := by linarith
    have h3 : (N * Θ) * (A * (Θ + 2 * T * vhi) - c) ≤ (N * Θ) * (-(c / 2)) :=
      mul_le_mul_of_nonneg_left h2 hNΘpos.le
    have h4 : (N * Θ) * (c / 2) = 2 * (Θ * vhi) := by
      rw [hN]; field_simp; ring
    have h5 : -(Θ * vhi) ≤ Φ t₀ := (abs_le.mp hΦabs).1
    linarith
  -- the intermediate value theorem
  obtain ⟨x, hxIcc, hxzero⟩ : ∃ x ∈ Set.Icc (t₀ - N * Θ) (t₀ + N * Θ), Φ x = 0 := by
    have hcont' : ContinuousOn Φ (Set.Icc (t₀ - N * Θ) (t₀ + N * Θ)) := hΦcont.continuousOn
    have h0 : (0 : ℝ) ∈ Set.Icc (Φ (t₀ + N * Θ)) (Φ (t₀ - N * Θ)) :=
      ⟨le_of_lt hright, le_of_lt hleft⟩
    have himg := intermediate_value_Icc' (a := t₀ - N * Θ) (b := t₀ + N * Θ)
      (by linarith [hNΘpos]) hcont' h0
    rcases himg with ⟨x, hxmem, hxeq⟩
    exact ⟨x, hxmem, hxeq⟩
  have hxabs : |x - t₀| ≤ N * Θ := by
    rw [Set.mem_Icc] at hxIcc
    rw [abs_le]
    constructor <;> linarith [hxIcc.1, hxIcc.2]
  have hxwin : x ∈ Set.Ioo (c₀ - T) (c₀ + T) := by
    rw [Set.mem_Ioo]
    have h3 : |x - c₀| ≤ T / 4 + T / 4 := by
      have h4 : |x - c₀| ≤ |x - t₀| + |t₀ - c₀| := abs_sub_le x t₀ c₀
      linarith [hxabs, ht₀]
    have h4 := abs_le.mp h3
    constructor <;> linarith
  refine ⟨x, ⟨hxwin, ?_, hxabs, ?_⟩, ?_, ?_⟩
  · simpa [hΦ] using hxzero
  · have h1 : ‖q - r x‖ ≤ ‖q - r t₀‖ + ‖r t₀ - r x‖ := by
      have he : q - r x = (q - r t₀) + (r t₀ - r x) := by abel
      rw [he]; exact norm_add_le _ _
    have h2 : ‖r t₀ - r x‖ ≤ vhi * |t₀ - x| := by
      have h := hrlip t₀ x
      rwa [norm_sub_rev, abs_sub_comm] at h
    have h3 : |t₀ - x| ≤ N * Θ := by rw [abs_sub_comm]; exact hxabs
    have h4 : vhi * |t₀ - x| ≤ vhi * (N * Θ) := mul_le_mul_of_nonneg_left h3 hvhi.le
    have h5 : κ = 1 + vhi * N := hκ
    have h6 : (1 + vhi * N) * Θ = Θ + vhi * (N * Θ) := by ring
    linarith
  · intro y hy hy0
    have hy0' : Φ y = 0 := by rw [hΦ]; exact hy0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := hstrict y x hy hxwin hlt
      rw [hy0', hxzero] at h
      exact lt_irrefl 0 h
    · have h := hstrict x y hxwin hy hlt
      rw [hy0', hxzero] at h
      exact lt_irrefl 0 h
  · intro y z hy hz hyz
    simpa [hΦ] using hstrict y z hy hz hyz


/-- **The base-map window for a smooth knot** (the `IsSmoothKnot` wrapper of
`Work.Drive.baseWindowStrict`). -/
theorem baseWindow {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ T N κ ηb : ℝ, 0 < T ∧ 0 < N ∧ 0 < κ ∧ 0 < ηb ∧
      ∀ c₀ : ℝ, ∀ Θ : ℝ, 0 < Θ → Θ ≤ ηb → ∀ t₀ : ℝ, |t₀ - c₀| ≤ T / 4 →
      ∀ q : Space, ‖q - r t₀‖ ≤ Θ →
        ∃ x : ℝ, (x ∈ Set.Ioo (c₀ - T) (c₀ + T) ∧
            inner ℝ (q - r x) (velocity r x) = 0 ∧
            |x - t₀| ≤ N * Θ ∧ ‖q - r x‖ ≤ κ * Θ) ∧
          (∀ y : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) →
            inner ℝ (q - r y) (velocity r y) = 0 → y = x) ∧
          (∀ y z : ℝ, y ∈ Set.Ioo (c₀ - T) (c₀ + T) → z ∈ Set.Ioo (c₀ - T) (c₀ + T) →
            y < z → inner ℝ (q - r z) (velocity r z) < inner ℝ (q - r y) (velocity r y)) := by
  obtain ⟨m, vhi, A, hm, hvhi, hA, hmin, hspd, hvlip⟩ := knotC2Bounds hr
  obtain ⟨δ, c, hδ, hc, hchord⟩ := knot_tangent_chord_bound hr
  have hrlip : ∀ x y : ℝ, ‖r y - r x‖ ≤ vhi * |y - x| :=
    lipOfDerivBound
      (fun t => ((hr.smooth.differentiable (by simp)) t).hasDerivAt) (fun t => hspd t)
  have hvlip' : ∀ x y : ℝ, ‖velocity r y - velocity r x‖ ≤ A * |y - x| := by
    intro x y
    have h := hvlip x y
    rwa [norm_sub_rev] at h
  have hcont : ∀ q : Space, Continuous fun t : ℝ => inner ℝ (q - r t) (velocity r t) := by
    intro q
    exact (continuous_const.sub hr.smooth.continuous).inner (hr.smooth.continuous_deriv le_top)
  exact baseWindowStrict hvhi hA.le hc hδ (fun t => hspd t) hvlip' hrlip
    (fun y z hyz hyz' => hchord y z hyz hyz') hcont

end

end Work.Drive
