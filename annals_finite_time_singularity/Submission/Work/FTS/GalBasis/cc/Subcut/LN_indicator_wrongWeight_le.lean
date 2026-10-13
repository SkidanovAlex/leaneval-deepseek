import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc.Subcut

/-! ## Elementary angular estimates

On the layer `LN N` (`N ≥ 1`) the angle `θ` stays a definite distance from `0` and from `π/2`, so
`sin(2θ)` is bounded below by a positive constant depending only on `N`.  The exact lower bound used
below is `4/(π (N+1))`, obtained from Jordan's inequality `(2/π) x ≤ sin x` on `[0, π/2]` applied to
`min (2θ) (π - 2θ)`. -/

/-- **Jordan's inequality, bilateral form.**  For `a > 0` with `6 a ≤ π` and `x ∈ [2a, 4a]` one has
`4a/π ≤ sin x`.  If `x ≤ π/2` this is Jordan's inequality at `x`, and if `x ≥ π/2` it is Jordan's
inequality at `π - x ∈ [2a, π/2]` (`6 a ≤ π` ensures `π - 4a ≥ 2a`), together with
`sin (π - x) = sin x`. -/
private lemma four_div_pi_mul_self_le_sin {a x : ℝ} (ha : 0 < a) (h6 : 6 * a ≤ Real.pi)
    (hx : 2 * a ≤ x) (hx2 : x ≤ 4 * a) : 4 * a / Real.pi ≤ Real.sin x := by
  have h4 : 4 * a ≤ Real.pi := by linarith
  by_cases hc : x ≤ Real.pi / 2
  · have h := Real.mul_le_sin (x := x) (by linarith) hc
    have h2 : 2 / Real.pi * (2 * a) ≤ 2 / Real.pi * x :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    have h3 : 4 * a / Real.pi = 2 / Real.pi * (2 * a) := by ring
    linarith
  · push Not at hc
    have h := Real.mul_le_sin (x := Real.pi - x) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at h
    have h2 : 2 / Real.pi * (2 * a) ≤ 2 / Real.pi * (Real.pi - x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 4 * a / Real.pi = 2 / Real.pi * (2 * a) := by ring
    linarith

/-- Version of `four_div_pi_mul_self_le_sin` with the scale parameter written as `1/b`. -/
private lemma four_div_pi_mul_div_le_sin {b x : ℝ} (hb : 0 < b) (h6 : 6 ≤ Real.pi * b)
    (hx : 2 / b ≤ x) (hx2 : x ≤ 4 / b) : 4 / (Real.pi * b) ≤ Real.sin x := by
  have ha : 0 < 1 / b := by positivity
  have h6a : 6 * (1 / b) ≤ Real.pi := by
    rw [show (6 : ℝ) * (1 / b) = 6 / b by ring, div_le_iff₀ hb]
    linarith
  have h1 : 2 * (1 / b) ≤ x := by
    rw [show (2 : ℝ) * (1 / b) = 2 / b by ring]; exact hx
  have h2 : x ≤ 4 * (1 / b) := by
    rw [show (4 : ℝ) * (1 / b) = 4 / b by ring]; exact hx2
  have hmain := four_div_pi_mul_self_le_sin ha h6a h1 h2
  have heq : 4 * (1 / b) / Real.pi = 4 / (Real.pi * b) := by field_simp
  rwa [heq] at hmain

/-- **The angular lower bound on the layers.**  For `N ≥ 1` and `θ ∈ LN N`,
`sin (2θ) ≥ 4/(π (N+1)) > 0`.  Both layers `[tlo N, 2/(N+1)]` and
`[π/2 - 2/(N+1), thi N]` are mirror images of one another about `π/4`, and `2θ` (resp. `π - 2θ`)
lies in `[2/(N+1), 4/(N+1)]`, so `four_div_pi_mul_div_le_sin` applies. -/
private lemma four_div_pi_mul_tlo_le_sin_two {N : ℕ} (hN : 1 ≤ N) {θ : ℝ}
    (hθ : θ ∈ Work.FTS.GalBasis.cc.LN N) :
    4 / (Real.pi * ((N : ℝ) + 1)) ≤ Real.sin (2 * θ) := by
  have hb : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h6 : 6 ≤ Real.pi * ((N : ℝ) + 1) := by nlinarith [Real.pi_gt_three]
  rcases hθ with hθ | hθ
  · rw [Work.FTS.GalBasis.cc.tlo] at hθ
    refine four_div_pi_mul_div_le_sin hb h6 ?_ ?_
    · have hmul := mul_le_mul_of_nonneg_left hθ.1 (by norm_num : (0 : ℝ) ≤ 2)
      have e : (2 : ℝ) * (1 / ((N : ℝ) + 1)) = 2 / ((N : ℝ) + 1) := by ring
      rwa [e] at hmul
    · have hmul := mul_le_mul_of_nonneg_left hθ.2 (by norm_num : (0 : ℝ) ≤ 2)
      have e : (2 : ℝ) * (2 / ((N : ℝ) + 1)) = 4 / ((N : ℝ) + 1) := by ring
      rwa [e] at hmul
  · rw [Work.FTS.GalBasis.cc.thi] at hθ
    have hmul2 := mul_le_mul_of_nonneg_left hθ.2 (by norm_num : (0 : ℝ) ≤ 2)
    have e2 : (2 : ℝ) * (Real.pi / 2 - 1 / ((N : ℝ) + 1))
        = Real.pi - 2 / ((N : ℝ) + 1) := by ring
    rw [e2] at hmul2
    have hx1 : 2 / ((N : ℝ) + 1) ≤ Real.pi - 2 * θ := by
      have h' := sub_le_sub_left hmul2 Real.pi
      rwa [sub_sub_cancel] at h'
    have hmul1 := mul_le_mul_of_nonneg_left hθ.1 (by norm_num : (0 : ℝ) ≤ 2)
    have e1 : (2 : ℝ) * (Real.pi / 2 - 2 / ((N : ℝ) + 1))
        = Real.pi - 4 / ((N : ℝ) + 1) := by ring
    rw [e1] at hmul1
    have hx2 : Real.pi - 2 * θ ≤ 4 / ((N : ℝ) + 1) := by
      have h' := sub_le_sub_left hmul1 Real.pi
      rw [sub_sub_cancel] at h'
      linarith
    have hmain := four_div_pi_mul_div_le_sin hb h6 hx1 hx2
    rwa [Real.sin_pi_sub] at hmain

/-! ## The weight comparison -/

/-- `(s^{-γ/2})² = s^{-γ}` for `s > 0`. -/
private lemma rpow_sq_neg_half {s γ : ℝ} (hs : 0 < s) : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
  congr 1
  ring

/-- **The pure weight comparison.**  For `0 < s ≤ 1`, `0 < sN ≤ s` and arbitrary exponents `η, γ`,
the wrong-weight slot with parameter `γ` is bounded by `max 1 (sN^{η-γ})` times the pure slot with
parameter `η`:
`(A (W s^{-γ/2}))² ≤ max 1 (sN^{η-γ}) · (A (W / s^{η/2}))²`.
Indeed both sides are `(A W)² s^{-γ}` resp. `(A W)² s^{-η}` and `s^{η-γ} ≤ max 1 (sN^{η-γ})`
(either `η - γ ≥ 0`, where `s^{η-γ} ≤ 1`, or `η - γ ≤ 0`, where `s^{η-γ} ≤ sN^{η-γ}`). -/
private lemma slot_rpow_le {A W s sN η γ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hsN : 0 < sN) (hsNs : sN ≤ s) :
    (A * (W * s ^ (-(γ / 2)))) ^ 2 ≤ max 1 (sN ^ (η - γ)) * (A * (W / s ^ (η / 2))) ^ 2 := by
  have hsqγ : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := rpow_sq_neg_half hs
  have hsqη : (s ^ (-(η / 2))) ^ 2 = s ^ (-η) := rpow_sq_neg_half hs
  have hdiv : W / s ^ (η / 2) = W * s ^ (-(η / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hs.le]
  have h1 : (A * (W * s ^ (-(γ / 2)))) ^ 2 = (A * W) ^ 2 * s ^ (-γ) := by
    rw [show (A * (W * s ^ (-(γ / 2)))) ^ 2 = (A * W) ^ 2 * (s ^ (-(γ / 2))) ^ 2 from by
      ring, hsqγ]
  have h2 : (A * (W / s ^ (η / 2))) ^ 2 = (A * W) ^ 2 * s ^ (-η) := by
    rw [hdiv]
    rw [show (A * (W * s ^ (-(η / 2)))) ^ 2 = (A * W) ^ 2 * (s ^ (-(η / 2))) ^ 2 from by
      ring, hsqη]
  rw [h1, h2]
  have hsplit : s ^ (-γ) = s ^ (-η) * s ^ (η - γ) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hb : s ^ (η - γ) ≤ max 1 (sN ^ (η - γ)) := by
    by_cases he : 0 ≤ η - γ
    · exact le_trans (Real.rpow_le_one hs.le hs1 he) (le_max_left 1 _)
    · push Not at he
      exact le_trans (Real.rpow_le_rpow_of_nonpos hsN hsNs (le_of_lt he)) (le_max_right 1 _)
  have hkey : s ^ (-γ) ≤ max 1 (sN ^ (η - γ)) * s ^ (-η) := by
    rw [hsplit]
    calc s ^ (-η) * s ^ (η - γ) ≤ s ^ (-η) * max 1 (sN ^ (η - γ)) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hs.le _)
      _ = max 1 (sN ^ (η - γ)) * s ^ (-η) := by ring
  calc (A * W) ^ 2 * s ^ (-γ)
      ≤ (A * W) ^ 2 * (max 1 (sN ^ (η - γ)) * s ^ (-η)) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = max 1 (sN ^ (η - γ)) * ((A * W) ^ 2 * s ^ (-η)) := by ring

/-- On the two angular layers `LN N` the wrong-weight slot `D_z^b f · Wt α` is bounded, up to a constant
`κ N` depending only on `N`, by the *pure* `D_z`-slot `D_z^b f · w / sin(2θ)^{η/2}` of `HkIntegrand`.

Indeed `Wt α z θ = w z · sin(2θ)^{-γ/2}` with `γ = Work.Spaces.gam α`, so both sides carry the same factors
`(D_z^b f)² w z²` and the ratio is `sin(2θ)^{η-γ}` with `η = Work.Spaces.eta = 99/100`; for `N ≥ 1` the layer is
contained in `(0, π/2)` (`tlo N > 0`, `thi N < π/2`), where `sin(2θ) ≥ s_N > 0`, so `sin(2θ)^{η-γ} ≤ κ N` with
`κ N := max 1 (s_N^{η-γ})`.  Off `LN N` the indicator kills the left side.  The `N ≥ 1` guard is needed (`N = 0`
has `π/2 ∈ LN 0 ∩ Iθ`). -/
theorem LN_indicator_wrongWeight_le {α : ℝ} {f : Work.FTS.Galerkin.Fn} {b : ℕ} :
    ∃ κ : ℕ → ℝ, (∀ N : ℕ, 0 < κ N) ∧ ∀ N : ℕ, 1 ≤ N → ∀ z θ : ℝ, 0 < z →
      θ ∈ Work.Spaces.Iθ →
      (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ κ N * (Work.Spaces.DzIter b f z θ *
            (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  refine ⟨fun N => max 1 ((4 / (Real.pi * ((N : ℝ) + 1))) ^ (Work.Spaces.eta - Work.Spaces.gam α)),
    fun N => lt_of_lt_of_le zero_lt_one (le_max_left 1 _), ?_⟩
  intro N hN z θ hz hθ
  by_cases hl : θ ∈ Work.FTS.GalBasis.cc.LN N
  · have hind : (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ = 1 := by
      rw [Set.indicator_of_mem hl]
    rw [hind, one_mul]
    have hsN : 0 < 4 / (Real.pi * ((N : ℝ) + 1)) := by positivity
    have hbound := four_div_pi_mul_tlo_le_sin_two hN hl
    have hsin : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hsN hbound
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hkey := slot_rpow_le (A := Work.Spaces.DzIter b f z θ) (W := Work.Spaces.w z)
      (s := Real.sin (2 * θ)) (sN := 4 / (Real.pi * ((N : ℝ) + 1)))
      (η := Work.Spaces.eta) (γ := Work.Spaces.gam α) hsin hsin1 hsN hbound
    simpa only [Work.Spaces.Wt, Work.Spaces.wTheta] using hkey
  · have hind : (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ = 0 := by
      rw [Set.indicator_of_notMem hl]
    rw [hind, zero_mul]
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))) (sq_nonneg _)

end Work.FTS.GalBasis.cc.Subcut
