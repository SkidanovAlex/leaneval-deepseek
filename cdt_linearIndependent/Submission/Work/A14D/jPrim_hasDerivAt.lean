import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.C17g.segment_primitive

namespace Work.A14D

open Complex Metric

/-! ## The elementary differentiability of the building blocks on `ball (1/9) δ`

These are the (private elsewhere) computations of `Work.A14D.exists_J_aux`: since `δ ≤ 1/20`,
the point `1` (pole of `yC`, `dyC`) and the point `0` (zero of `yC`) lie outside the ball. -/

private lemma yC_diffOn_ball {c : ℂ} {r : ℝ} (h : (1 : ℂ) ∉ ball c r) :
    DifferentiableOn ℂ yC (ball c r) := by
  unfold yC
  exact (differentiableOn_id.pow 2).div
    (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun hz1 => h (by rwa [hz1] at hz)))

private lemma yC_ne_ball {c : ℂ} {r : ℝ} (h0 : (0 : ℂ) ∉ ball c r) (h1 : (1 : ℂ) ∉ ball c r) :
    ∀ z ∈ ball c r, yC z ≠ 0 := by
  intro z hz hz0
  have hz1 : z ≠ 1 := fun hh => h1 (by rwa [hh] at hz)
  have h : z ^ 2 = 0 := by
    have hh := hz0
    rw [yC] at hh
    field_simp at hh
    simpa using hh
  have hz0' : z = 0 := sq_eq_zero_iff.mp h
  rw [hz0'] at hz
  exact h0 hz

private lemma dyC_diffOn_ball {c : ℂ} {r : ℝ} (h : (1 : ℂ) ∉ ball c r) :
    DifferentiableOn ℂ dyC (ball c r) := by
  unfold dyC
  exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
    ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun hh => h (by rwa [hh] at hz))))

private lemma zero_not_mem_ball_ninth {δ : ℝ} (hδ20 : δ ≤ 1 / 20) :
    (0 : ℂ) ∉ ball ninth δ := by
  intro hmem
  have h := hmem
  rw [Metric.mem_ball, Complex.dist_eq, zero_sub] at h
  have hle : ‖ninth‖ = 1 / 9 := by norm_num [ninth]
  rw [norm_neg, hle] at h
  linarith

private lemma one_not_mem_ball_ninth {δ : ℝ} (hδ20 : δ ≤ 1 / 20) :
    (1 : ℂ) ∉ ball ninth δ := by
  intro hmem
  have h := hmem
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hle : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by norm_num [ninth]
  rw [hle] at h
  linarith

/-- The integrand `(yC ·)^{-j}·dyC·y9` of `jPrim` is holomorphic on the disc `ball (1/9) δ`. -/
private lemma integrand_diffOn {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) (j : ℕ) :
    DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ j * dyC z * y9 z) (ball ninth δ) := by
  obtain ⟨hδpos, hδ20, hy9d, -, -⟩ := hY
  have h0 := zero_not_mem_ball_ninth hδ20
  have h1 := one_not_mem_ball_ninth hδ20
  have hYd : DifferentiableOn ℂ yC (ball ninth δ) := yC_diffOn_ball h1
  have hYne : ∀ z ∈ ball ninth δ, yC z ≠ 0 := yC_ne_ball h0 h1
  have hDd : DifferentiableOn ℂ dyC (ball ninth δ) := dyC_diffOn_ball h1
  have hinv : DifferentiableOn ℂ (fun z => (yC z)⁻¹) (ball ninth δ) := hYd.inv hYne
  exact ((hinv.pow j).mul hDd).mul hy9d

/-- The canonical primitives `jPrim y9 i = primSeg (fun z => (yC z)⁻¹ ^ i * dyC z * y9 z) ninth`
(defined in `Submission.Work.A14D.LC_setup`) have the derivative required by the conclusion of
`relation_to_LC_A`; the companion `Work.A14D.jPrim_ninth` (already proved in
`Submission.Work.A14D.relation_to_LC_A`) gives the normalisation, so together with
`Work.A14D.prim_unique` this pins the existential `J` of the target to `jPrim`, which is what
`Work.A14D.sum_jumpCoeff_eq` consumes.

Route: the integrand `g := fun z => (yC z)⁻¹ ^ (i:ℕ) * dyC z * y9 z` is holomorphic on
`Metric.ball (1/9) δ` (the computation is inside the proved `Work.A14D.exists_J_aux`: `Y9` gives
`δ ≤ 1/20`, so `0, 1 ∉ Metric.ball ninth δ`), so the proved `Work.C17g.segment_primitive` (with
`S = Metric.ball ninth δ` convex and open, base point `1/9`) gives
`HasDerivAt (fun z => (z - ninth) • ∫ t in 0..1, g (ninth + t • (z - ninth))) (g z) z`; it remains
to identify `jPrim y9 (i : ℕ)` with that function: this is the rewriting
`∫ t, g (ninth + ↑t * (w - ninth)) * (w - ninth) = (w - ninth) • ∫ t, g (ninth + t • (w - ninth))`
(`intervalIntegral.integral_mul_const`, `smul_eq_mul`, and `Complex.ofReal_smul` for the real
scalar action inside the integrand), followed by `HasDerivAt.congr_of_eventuallyEq`. -/
theorem jPrim_hasDerivAt {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) (i : Fin 3) :
    ∀ z ∈ Metric.ball ninth δ, HasDerivAt (jPrim y9 (i : ℕ)) ((yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z) z := by
  have hgd : DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z) (ball ninth δ) :=
    integrand_diffOn hY (i : ℕ)
  obtain ⟨hδpos, -, -, -, -⟩ := hY
  -- The segment primitive of the integrand, from the convex/open ball `ball (1/9) δ`.
  obtain ⟨-, hkey⟩ :=
    Work.C17g.segment_primitive (E := ℂ) (convex_ball ninth δ) isOpen_ball
      (Metric.mem_ball_self hδpos) hgd
  intro z hz
  refine (hkey z hz).congr_of_eventuallyEq ?_
  -- `jPrim` is the same segment integral, written with a multiplication instead of a scalar action.
  filter_upwards [isOpen_ball.mem_nhds hz] with w _
  rw [jPrim, primSeg]
  have hA : (∫ t in (0 : ℝ)..1,
        ((yC (ninth + (t : ℂ) * (w - ninth)))⁻¹ ^ (i : ℕ) * dyC (ninth + (t : ℂ) * (w - ninth))
          * y9 (ninth + (t : ℂ) * (w - ninth))))
      = ∫ t in (0 : ℝ)..1,
        ((yC (ninth + t • (w - ninth)))⁻¹ ^ (i : ℕ) * dyC (ninth + t • (w - ninth))
          * y9 (ninth + t • (w - ninth))) :=
    intervalIntegral.integral_congr fun t _ => by rw [Complex.real_smul]
  rw [intervalIntegral.integral_mul_const, hA, smul_eq_mul, mul_comm]

end Work.A14D
