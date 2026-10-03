import Mathlib
import Submission.Work.Fatou.Setup

/-!
# The inverse of a near-translation on the central strip

For a near-translation `F` on Shishikura's region `Qreg b₁ b₂` the derivative satisfies
`‖F' - 1‖ ≤ 1/32` everywhere on `Qreg`.  The vertical strip
`S = {x₀ - 1/8 < Re z < x₀ + 1/8}` is convex and contained in `Qreg`, so the mean value
inequality shows that `F` is a small perturbation of the identity on `S`, hence injective
there.  Consequently `F` has a genuine inverse `finv` on `F '' S`; since `deriv F ≠ 0` and `F` is
analytic on the (open) strip, the inverse is analytic on `F '' S` by the holomorphic inverse
function theorem (`analyticAt_comp_iff_of_deriv_ne_zero`).

This is the inverse used for the "negative" transition maps `F⁻¹` of the surface `XF`.
-/

namespace Work.Fatou.Surface

open Set Filter
open scoped Topology

noncomputable section

/-- The open vertical strip of half-width `1/8` around `x₀`. -/
def strip (x₀ : ℝ) : Set ℂ := {z : ℂ | x₀ - 1 / 8 < z.re ∧ z.re < x₀ + 1 / 8}

theorem isOpen_strip (x₀ : ℝ) : IsOpen (strip x₀) := by
  have h1 : IsOpen {z : ℂ | x₀ - 1 / 8 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < x₀ + 1 / 8} :=
    isOpen_lt Complex.continuous_re continuous_const
  exact h1.inter h2

theorem convex_strip (x₀ : ℝ) : Convex ℝ (strip x₀) :=
  (convex_halfSpace_re_gt (x₀ - 1 / 8)).inter (convex_halfSpace_re_lt (x₀ + 1 / 8))

/-- The strip `x₀ ± 1/8` is contained in `Qreg` (the closed strip `x₀ ± 1/8` is, and the open
strip is contained in it). -/
theorem strip_subset_Qreg {b₁ b₂ : Option ℂ} (h : MandelDim.QAdm b₁ b₂) :
    strip (Work.Fatou.xOf b₁ b₂) ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  exact Work.Fatou.strip_eighth_subset_Qreg h ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/-- **Injectivity from a derivative bound.**  If `F` is complex differentiable on an open convex
set `S` and `‖F' - 1‖ ≤ 1/32` on `S`, then `F` is injective on `S`.  Indeed `F - id` is
`1/32`-Lipschitz by the mean value inequality, so `F x = F y` forces `‖x - y‖ = 0`. -/
theorem injOn_of_deriv_close {S : Set ℂ} (hS : IsOpen S) (hSc : Convex ℝ S) {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F S) (hbound : ∀ z ∈ S, ‖deriv F z - 1‖ ≤ 1 / 32) :
    Set.InjOn F S := by
  intro x hx y hy hxy
  have hdat : ∀ z ∈ S, DifferentiableAt ℂ F z :=
    fun z hz => (hd z hz).differentiableAt (IsOpen.mem_nhds hS hz)
  have hderiv : ∀ z ∈ S, deriv (fun w => F w - w) z = deriv F z - 1 := by
    intro z hz
    have h : (fun w => F w - w) = (F - id) := rfl
    rw [h, deriv_sub (hdat z hz) differentiableAt_id, deriv_id]
  have hMVT := hSc.norm_image_sub_le_of_norm_deriv_le (f := fun w => F w - w) (C := 1 / 32)
    (fun z hz => (hdat z hz).sub differentiableAt_id)
    (fun z hz => by rw [hderiv z hz]; exact hbound z hz) hx hy
  have h1 : ‖x - y‖ ≤ 1 / 32 * ‖x - y‖ := by
    have hc := (by simpa [hxy] using hMVT : ‖x - y‖ ≤ 1 / 32 * ‖y - x‖)
    rwa [norm_sub_rev y x] at hc
  have h3 : ‖x - y‖ = 0 := by
    have h2 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- **Holomorphy of a left inverse.**  If `F` is analytic at `a` with `deriv F a ≠ 0` and `g` is
a left inverse of `F` near `a`, then `g` is analytic at `F a`.  This is the holomorphic inverse
function theorem, applied to the composite `g ∘ F`, which agrees with the identity near `a`. -/
theorem analyticAt_of_leftInverse {F g : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a)
    (hF' : deriv F a ≠ 0) (h : ∀ᶠ x in 𝓝 a, g (F x) = x) : AnalyticAt ℂ g (F a) := by
  have h' : (fun x => g (F x)) =ᶠ[𝓝 a] id := h
  exact (analyticAt_comp_iff_of_deriv_ne_zero hF hF').mp (analyticAt_id.congr h'.symm)

/-- On the open vertical strip `S = {x₀ - 1/8 < Re z < x₀ + 1/8}` (which is convex and contained
in `Qreg`), the near-translation `F` is injective with an open image and has a holomorphic inverse
there.  This is the inverse used for the "negative" transition maps `F⁻¹` of the surface `XF`.
The injectivity follows from `‖F' - 1‖ ≤ 1/32` on the convex strip, and the holomorphy of the
inverse from the (holomorphic) inverse function theorem, since `deriv F ≠ 0` on `Qreg`. -/
theorem localInverse {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) :
    ∃ finv : ℂ → ℂ,
      (∀ z : ℂ, Work.Fatou.xOf b₁ b₂ - 1 / 8 < z.re → z.re < Work.Fatou.xOf b₁ b₂ + 1 / 8 →
        finv (F z) = z) ∧
      (∀ w ∈ F '' {z : ℂ | Work.Fatou.xOf b₁ b₂ - 1 / 8 < z.re ∧ z.re < Work.Fatou.xOf b₁ b₂ + 1 / 8},
        F (finv w) = w) ∧
      ContDiffOn ℂ 1 finv
        (F '' {z : ℂ | Work.Fatou.xOf b₁ b₂ - 1 / 8 < z.re ∧ z.re < Work.Fatou.xOf b₁ b₂ + 1 / 8}) := by
  set S : Set ℂ :=
    {z : ℂ | Work.Fatou.xOf b₁ b₂ - 1 / 8 < z.re ∧ z.re < Work.Fatou.xOf b₁ b₂ + 1 / 8} with hSdef
  have hSQ : S ⊆ MandelDim.Qreg b₁ b₂ := by
    rw [hSdef]
    exact strip_subset_Qreg hadm
  have hSopen : IsOpen S := by
    rw [hSdef]; exact isOpen_strip (Work.Fatou.xOf b₁ b₂)
  have hSconv : Convex ℝ S := by
    rw [hSdef]; exact convex_strip (Work.Fatou.xOf b₁ b₂)
  have hD : DifferentiableOn ℂ F S := hF.1.mono hSQ
  have hInj : Set.InjOn F S :=
    injOn_of_deriv_close hSopen hSconv hD (fun z hz => (hF.2 z (hSQ hz)).2)
  refine ⟨Function.invFunOn F S, ?_, ?_, ?_⟩
  · intro z hz1 hz2
    exact hInj.leftInvOn_invFunOn ⟨hz1, hz2⟩
  · intro w hw
    exact Function.invFunOn_eq hw
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := hw
    have hFa : AnalyticAt ℂ F a := hD.analyticAt (IsOpen.mem_nhds hSopen ha)
    have hne : deriv F a ≠ 0 := by
      intro h0
      have h32 := (hF.2 a (hSQ ha)).2
      rw [h0] at h32; norm_num at h32
    have hev : ∀ᶠ x in 𝓝 a, Function.invFunOn F S (F x) = x :=
      Filter.mem_of_superset (IsOpen.mem_nhds hSopen ha)
        (fun x hx => hInj.leftInvOn_invFunOn hx)
    exact (analyticAt_of_leftInverse hFa hne hev).contDiffAt.contDiffWithinAt

end

end Work.Fatou.Surface
