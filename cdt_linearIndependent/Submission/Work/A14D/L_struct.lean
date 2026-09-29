import Mathlib
import Submission.Work.A14.defs

/-!
# `Work.A14D.L_struct`

The local structural model of `Hfun a b c` at `x = 1` (`hid`, holomorphic on the lens
`lens1 δ = ball 1 δ ∩ ball 0 1`) propagates to the continuation `HL` of `Hfun a b c` on the
lower half-plane `SL`: on `SL ∩ ball 1 δ ∩ {Im < 0}` the function `HL` equals the model
`e₀ + e₁·log(1-z) + e₂·log(1-z)²`.

Both sides are complex analytic on the open, convex (hence connected) set
`SL ∩ ball 1 δ ∩ {Im < 0}`: `HL` because it is differentiable on the half-plane `SL ⊇ ·`, and the
model because `log(1-·)` is holomorphic on the lower half-plane (`1 - z` has positive imaginary
part there) while the `eᵢ` are holomorphic on `ball 1 δ`.  On the non-empty open subset
`lens1 δ ∩ SL ∩ {Im < 0}` both agree by `hid` and `hHL`; the identity theorem concludes.
-/

open Complex Metric Filter
open scoped Topology Real

noncomputable section
namespace Work.A14D

/-- `ell = log (1 - ·)` is complex differentiable on any set contained in the lower half-plane. -/
private lemma differentiableOn_ell_of_im_neg {s : Set ℂ} (hs : ∀ z ∈ s, z.im < 0) :
    DifferentiableOn ℂ ell s := by
  intro z hz
  have h1 : (1 - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    have h : (1 - z).im = -z.im := by simp
    rw [h]
    exact neg_ne_zero.mpr (ne_of_lt (hs z hz))
  have hd : DifferentiableAt ℂ (fun t : ℂ => Complex.log (1 - t)) z :=
    (Complex.differentiableAt_log h1).comp z
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
  exact hd.differentiableWithinAt

/-- The local model `e₀ + e₁·ℓ + e₂·ℓ²` is differentiable wherever the `eᵢ` are and `Im < 0`. -/
private lemma differentiableOn_model {s : Set ℂ} (hs : ∀ z ∈ s, z.im < 0)
    {e0 e1 e2 : ℂ → ℂ}
    (he0 : DifferentiableOn ℂ e0 s) (he1 : DifferentiableOn ℂ e1 s)
    (he2 : DifferentiableOn ℂ e2 s) :
    DifferentiableOn ℂ (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) s := by
  have hell := differentiableOn_ell_of_im_neg hs
  exact (he0.add (he1.mul hell)).add (he2.mul (hell.pow 2))

/-- A point of the open set `lens1 δ ∩ SL ∩ {Im < 0}` exists for every `δ > 0`. -/
private lemma exists_anchor {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℂ, z ∈ Metric.ball (1 : ℂ) δ ∧ z ∈ Metric.ball (0 : ℂ) 1 ∧ z ∈ SL ∧ z.im < 0 := by
  set t : ℝ := min δ 1 / 2 with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]; have : 0 < min δ 1 := lt_min hδ zero_lt_one; positivity
  have ht_δ : t ≤ δ / 2 := by
    rw [ht_def]; have : min δ 1 ≤ δ := min_le_left _ _; linarith
  have ht_half : t ≤ 1 / 2 := by
    rw [ht_def]; have : min δ 1 ≤ 1 := min_le_right _ _; linarith
  refine ⟨Complex.mk (1 - t) (-(t/4)), ?_, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hnorm : Complex.normSq (Complex.mk (1 - t) (-(t/4)) - 1) = t^2 + (t/4)^2 := by
      rw [Complex.normSq_apply]; simp; ring
    have hs : ‖Complex.mk (1 - t) (-(t/4)) - 1‖ ^ 2 < δ ^ 2 := by
      rw [Complex.sq_norm, hnorm]; nlinarith [ht_δ, hδ]
    have := sq_lt_sq.mp hs
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ] at this
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hnorm : Complex.normSq (Complex.mk (1 - t) (-(t/4)) - 0) = (1-t)^2 + (t/4)^2 := by
      rw [Complex.normSq_apply]; simp; ring
    have hs : ‖Complex.mk (1 - t) (-(t/4)) - 0‖ ^ 2 < (1:ℝ) ^ 2 := by
      rw [Complex.sq_norm, hnorm]; nlinarith [ht_pos, ht_half]
    have := sq_lt_sq.mp hs
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos (by norm_num : (0:ℝ) < 1)] at this
  · show (Complex.mk (1 - t) (-(t/4))).im < ((Complex.mk (1 - t) (-(t/4))).re - 1) / 8
    simp; linarith [ht_pos]
  · show (Complex.mk (1 - t) (-(t/4))).im < 0
    simp; linarith [ht_pos]

theorem L_struct {a b c : ℤ} {δ : ℝ} (hδ : 0 < δ)
    {e0 e1 e2 : ℂ → ℂ}
    (he0 : DifferentiableOn ℂ e0 (Metric.ball (1:ℂ) δ))
    (he1 : DifferentiableOn ℂ e1 (Metric.ball (1:ℂ) δ))
    (he2 : DifferentiableOn ℂ e2 (Metric.ball (1:ℂ) δ))
    (hid : ∀ z ∈ Work.A14D.lens1 δ, Work.A14D.Hfun a b c z
        = e0 z + e1 z * Work.A14D.ell z + e2 z * Work.A14D.ell z ^ 2)
    {HL : ℂ → ℂ} (hHLd : DifferentiableOn ℂ HL Work.A14D.SL)
    (hHL : ∀ z ∈ Work.A14D.SL ∩ Metric.ball (0:ℂ) 1, HL z = Work.A14D.Hfun a b c z) :
    ∀ z ∈ Work.A14D.SL ∩ Metric.ball (1:ℂ) δ ∩ {z : ℂ | z.im < 0},
      HL z = e0 z + e1 z * Work.A14D.ell z + e2 z * Work.A14D.ell z ^ 2 := by
  set S : Set ℂ := SL ∩ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0} with hS
  have hSLopen : IsOpen SL := by
    show IsOpen {z : ℂ | z.im < (z.re - 1) / 8}
    exact isOpen_lt Complex.continuous_im (by continuity)
  have hSopen : IsOpen S := by
    rw [hS]
    exact (hSLopen.inter Metric.isOpen_ball).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hSLconv : Convex ℝ SL := by
    have h : SL = {z : ℂ | 1 < z.re - 8 * z.im} := by
      ext z
      show z.im < (z.re - 1) / 8 ↔ 1 < z.re - 8 * z.im
      constructor <;> intro hh <;> linarith
    rw [h]
    exact convex_halfSpace_gt (f := fun z : ℂ => z.re - 8 * z.im)
      ⟨by intro x y; simp; ring, by intro c x; simp; ring⟩ 1
  have hSconv : Convex ℝ S := by
    rw [hS]
    exact (hSLconv.inter (convex_ball 1 δ)).inter
      (convex_halfSpace_lt (f := fun z : ℂ => z.im)
        ⟨by intro x y; simp, by intro c x; simp⟩ 0)
  have hSpre : IsPreconnected S := hSconv.isPreconnected
  have hmodel : DifferentiableOn ℂ (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) S := by
    have hb : ∀ z ∈ S, z ∈ Metric.ball (1:ℂ) δ := by
      intro z hz; rw [hS] at hz; exact hz.1.2
    have hi : ∀ z ∈ S, z.im < 0 := by
      intro z hz; rw [hS] at hz; exact hz.2
    exact differentiableOn_model hi (he0.mono hb) (he1.mono hb) (he2.mono hb)
  have hHLd' : DifferentiableOn ℂ HL S := by
    apply hHLd.mono
    intro z hz; rw [hS] at hz; exact hz.1.1
  have hmodel_an : AnalyticOnNhd ℂ (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) S :=
    (Complex.analyticOnNhd_iff_differentiableOn hSopen).mpr hmodel
  have hHL_an : AnalyticOnNhd ℂ HL S :=
    (Complex.analyticOnNhd_iff_differentiableOn hSopen).mpr hHLd'
  obtain ⟨z₀, hz₀1, hz₀0, hz₀SL, hz₀im⟩ := exists_anchor hδ
  have hz₀S : z₀ ∈ S := by rw [hS]; exact ⟨⟨hz₀SL, hz₀1⟩, hz₀im⟩
  have hPopen : IsOpen ((lens1 δ ∩ SL) ∩ {z : ℂ | z.im < 0}) := by
    show IsOpen (((Metric.ball (1:ℂ) δ ∩ Metric.ball (0:ℂ) 1) ∩ SL) ∩ {z : ℂ | z.im < 0})
    exact ((Metric.isOpen_ball.inter Metric.isOpen_ball).inter hSLopen).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hz₀P : z₀ ∈ (lens1 δ ∩ SL) ∩ {z : ℂ | z.im < 0} :=
    ⟨⟨⟨hz₀1, hz₀0⟩, hz₀SL⟩, hz₀im⟩
  have hAgree : HL =ᶠ[𝓝 z₀] (fun z => e0 z + e1 z * ell z + e2 z * ell z ^ 2) := by
    apply Filter.mem_of_superset (hPopen.mem_nhds hz₀P)
    intro z hz
    exact (hHL z ⟨hz.1.2, hz.1.1.2⟩).trans (hid z hz.1.1)
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHL_an hmodel_an hSpre hz₀S hAgree

end Work.A14D
