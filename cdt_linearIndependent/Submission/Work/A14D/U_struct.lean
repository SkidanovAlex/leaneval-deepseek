import Mathlib
import Submission.Work.A14.defs

/-!
# `Work.A14D.U_struct`

Structure of the upper continuation `HU` of the `x`-side series `H = Hfun a b c` on the half-plane
`SU = {z | (1 - Re z)/8 < Im z}`.

`HU` is only known to be holomorphic on `SU` and to agree with `Hfun a b c` on
`SU ∩ ball 0 1`.  On the lens `lens1 δ = ball 1 δ ∩ ball 0 1` (in particular near the singular
point `x = 1`, where `H` involves the two branches of `log (1-x)`), `Hfun a b c` is known to be of
the form `e0 + e1·ℓ + e2·ℓ²` with `e0, e1, e2` holomorphic on `ball 1 δ` and `ℓ = log (1-z)`.

Since the branch cut of `ℓ` is the real half-line `[1, ∞)`, and the upper half-plane avoids it, the
combination `z ↦ e0 z + e1 z·ℓ z + e2 z·(ℓ z)²` is holomorphic on the open half-plane
`SU ∩ ball 1 δ ∩ {Im z > 0}`, as is `HU`; both agree on the non-empty open subset
`SU ∩ ball 1 δ ∩ ball 0 1 ∩ {Im z > 0}`.  That set is convex (hence preconnected), so the identity
theorem for holomorphic functions gives the conclusion.

Everything needed is proved below from `Mathlib` and `Work.A14.defs`; the only genuinely geometric
input is the existence of a point of `SU` in the upper half of the lens
(`exists_mem_SU_lens1_upper`, an explicit witness `(1 - t) + (t/2) I`, `t = min δ 1 / 2`).
-/

namespace Work.A14D

open Complex Metric
open scoped Topology

/-! ## 1. Elementary geometry of `SU` and of the branch `ℓ = log (1 - z)` -/

/-- `z ∈ SU ↔ 1 < 8·Im z + Re z` (the half-plane in linear normal form). -/
private lemma mem_SU_iff' {z : ℂ} : z ∈ SU ↔ 1 < 8 * z.im + z.re := by
  have h : z ∈ SU ↔ (1 - z.re) / 8 < z.im := Iff.rfl
  rw [h, div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)]
  constructor <;> intro h' <;> linarith

/-- `SU` is convex: it is the superlevel set `{1 < 8·Im + Re}` of a real-linear functional. -/
private lemma convex_SU' : Convex ℝ SU := by
  have h : SU = {z : ℂ | 1 < 8 * z.im + z.re} := by ext z; exact mem_SU_iff'
  rw [h]
  exact convex_halfSpace_gt ⟨by intro x y; simp; ring, by intro c x; simp; ring⟩ 1

/-- `SU` is open. -/
private lemma isOpen_SU' : IsOpen SU := by
  have h : SU = {z : ℂ | (1 - z.re) / 8 < z.im} := rfl
  rw [h]
  exact isOpen_lt (by fun_prop) (by fun_prop)

/-- On the open upper half-plane `log (1 - z)` is holomorphic: `1 - z` has negative imaginary
part there, hence lies in the slit plane. -/
private lemma differentiableOn_ell_im_pos {Ω : Set ℂ} (hΩ : ∀ z ∈ Ω, 0 < z.im) :
    DifferentiableOn ℂ ell Ω := by
  intro z hz
  have hsp : 1 - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    have h : (1 - z).im = -z.im := by simp
    rw [h]; linarith [hΩ z hz]
  exact ((Complex.differentiableAt_log hsp).comp z
    ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)).differentiableWithinAt

/-- For every `δ > 0` the lens `ball (1:ℂ) δ ∩ ball 0 1` contains a point of `SU` in the open
upper half-plane: an explicit witness is `(1 - t) + (t/2) I` with `t = min δ 1 / 2`. -/
private lemma exists_mem_SU_lens1_upper {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℂ, z ∈ SU ∧ z ∈ Metric.ball (1 : ℂ) δ ∧ z ∈ Metric.ball (0 : ℂ) 1 ∧ 0 < z.im := by
  set t : ℝ := min δ 1 / 2 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have htδ : t ≤ δ / 2 := by rw [ht]; linarith [min_le_left δ 1]
  have ht1 : t ≤ 1 / 2 := by rw [ht]; linarith [min_le_right δ 1]
  have h2 : ‖((t / 2 : ℝ) : ℂ) * Complex.I‖ = t / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    exact (RCLike.norm_ofReal (t / 2)).trans (abs_of_nonneg (by linarith))
  refine ⟨(1 - t) + (t / 2) * Complex.I, ?_, ?_, ?_, ?_⟩
  · rw [mem_SU_iff']
    have him : ((1 - t) + (t / 2) * Complex.I).im = t / 2 := by simp
    have hre : ((1 - t) + (t / 2) * Complex.I).re = 1 - t := by simp
    rw [him, hre]; linarith
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hsplit : (1 - t) + (t / 2) * Complex.I - 1
        = (-(t : ℂ)) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hsplit]
    have h1 : ‖(-(t : ℂ))‖ = t := by
      rw [norm_neg]
      exact (RCLike.norm_ofReal t).trans (abs_of_nonneg (le_of_lt ht0))
    calc ‖(-(t : ℂ)) + ((t / 2 : ℝ) : ℂ) * Complex.I‖
        ≤ ‖(-(t : ℂ))‖ + ‖((t / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = t + t / 2 := by rw [h1, h2]
      _ < δ := by linarith
  · rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
    have hsplit : (1 - t) + (t / 2) * Complex.I
        = (((1 - t : ℝ)) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hsplit]
    have h1 : ‖(((1 - t : ℝ)) : ℂ)‖ = 1 - t :=
      (RCLike.norm_ofReal (1 - t)).trans (abs_of_nonneg (by linarith))
    calc ‖(((1 - t : ℝ)) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I‖
        ≤ ‖(((1 - t : ℝ)) : ℂ)‖ + ‖((t / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 - t + t / 2 := by rw [h1, h2]
      _ < 1 := by linarith
  · have him : ((1 - t) + (t / 2) * Complex.I).im = t / 2 := by simp
    rw [him]; linarith

/-! ## 2. The structure of `HU` on `SU` -/

theorem U_struct {a b c : ℤ} {δ : ℝ} (hδ : 0 < δ)
    {e0 e1 e2 : ℂ → ℂ}
    (he0 : DifferentiableOn ℂ e0 (Metric.ball (1:ℂ) δ))
    (he1 : DifferentiableOn ℂ e1 (Metric.ball (1:ℂ) δ))
    (he2 : DifferentiableOn ℂ e2 (Metric.ball (1:ℂ) δ))
    (hid : ∀ z ∈ Work.A14D.lens1 δ, Work.A14D.Hfun a b c z
        = e0 z + e1 z * Work.A14D.ell z + e2 z * Work.A14D.ell z ^ 2)
    {HU : ℂ → ℂ} (hHUd : DifferentiableOn ℂ HU Work.A14D.SU)
    (hHU : ∀ z ∈ Work.A14D.SU ∩ Metric.ball (0:ℂ) 1, HU z = Work.A14D.Hfun a b c z) :
    ∀ z ∈ Work.A14D.SU ∩ Metric.ball (1:ℂ) δ ∩ {z : ℂ | 0 < z.im},
      HU z = e0 z + e1 z * Work.A14D.ell z + e2 z * Work.A14D.ell z ^ 2 := by
  set S : Set ℂ := SU ∩ Metric.ball (1:ℂ) δ ∩ {z : ℂ | 0 < z.im} with hSdef
  -- `S` is open, convex, hence preconnected
  have hSopen : IsOpen S := by
    rw [hSdef]
    exact (isOpen_SU'.inter Metric.isOpen_ball).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hSconv : Convex ℝ S := by
    rw [hSdef]
    exact (convex_SU'.inter (convex_ball (1:ℂ) δ)).inter (convex_halfSpace_im_gt 0)
  -- a point of `S` inside the unit disc, where `HU` and the combination agree by hypothesis
  obtain ⟨z0, hz0SU, hz0b1, hz0b0, hz0im⟩ := exists_mem_SU_lens1_upper hδ
  have hz0S : z0 ∈ S := by
    rw [hSdef]; exact ⟨⟨hz0SU, hz0b1⟩, hz0im⟩
  have hW : S ∩ Metric.ball (0:ℂ) 1 ∈ 𝓝 z0 :=
    (hSopen.inter Metric.isOpen_ball).mem_nhds ⟨hz0S, hz0b0⟩
  have heq : HU =ᶠ[𝓝 z0] (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) := by
    refine Filter.eventually_of_mem hW (fun z hz => ?_)
    obtain ⟨hzS, hzb0⟩ := hz
    rw [hSdef] at hzS
    obtain ⟨⟨hzSU, hzb1⟩, _hzim⟩ := hzS
    rw [hHU z ⟨hzSU, hzb0⟩, hid z ⟨hzb1, hzb0⟩]
  -- both sides are holomorphic on `S`
  have hHUan : AnalyticOnNhd ℂ HU S :=
    hHUd.mono (by rw [hSdef]; exact fun z hz => hz.1.1) |>.analyticOnNhd hSopen
  have hGdiff : DifferentiableOn ℂ (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) S := by
    have hsub : S ⊆ Metric.ball (1:ℂ) δ := by rw [hSdef]; exact fun z hz => hz.1.2
    have hell : DifferentiableOn ℂ ell S :=
      differentiableOn_ell_im_pos (fun z hz => by rw [hSdef] at hz; exact hz.2)
    exact ((he0.mono hsub).add ((he1.mono hsub).mul hell)).add
      ((he2.mono hsub).mul (hell.pow 2))
  have hGan : AnalyticOnNhd ℂ (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) S :=
    hGdiff.analyticOnNhd hSopen
  -- the identity theorem on the preconnected set `S`
  have hall := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHUan hGan
    hSconv.isPreconnected hz0S heq
  intro z hz
  rw [hSdef] at hz
  exact hall hz

end Work.A14D
