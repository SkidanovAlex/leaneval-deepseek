/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): smoothness and support of the first order
commutator coefficients appearing in the localized equation.

The localized distributional equation involves the multipliers `∂₀χ`, `∂₁χ` and
`ρ₀ = ∂₀∂₀χ + ∂₁∂₁χ - 5∂₀χ + tt·∂₁χ`.  For the Sobolev gain (`Q0.mulSob`) these must be smooth
with compact support; both facts follow from the corresponding facts for `χ` (and `tt`), using
`tsupport_fderiv_apply_subset` for the support and `ContDiff.contDiff_fderiv_apply` for the
smoothness.
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem finrank_E2 : Module.finrank ℝ E2 = 2 := by
  rw [finrank_euclideanSpace_fin]

/-- The zeroth-order commutator coefficient `Δχ - 5 ∂₀χ + tt ∂₁χ`. -/
def rho0 (χ tt : E2 → ℂ) : E2 → ℂ :=
  fun x => d0 (d0 χ) x + d1 (d1 χ) x - 5 * d0 χ x + tt x * d1 χ x

theorem contDiff_d0 {f : E2 → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ n (fun x => d0 f x) := by
  have h1 : ContDiff ℝ (n : ℕ∞ω) (fun p : E2 × E2 => (fderiv ℝ f p.1) p.2) :=
    ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := f)
      (n := ((n + 1 : ℕ) : ℕ∞ω)) (m := (n : ℕ∞ω)) (hf (n + 1)) (by push_cast; norm_num)
  have h2 : ContDiff ℝ (n : ℕ∞ω) (fun x : E2 => (fderiv ℝ f x) e0) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  have h3 : (fun x : E2 => d0 f x) = fun x : E2 => (fderiv ℝ f x) e0 := by
    funext x
    exact (hf 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rwa [h3]

theorem contDiff_d1 {f : E2 → ℂ} (hf : ∀ k : ℕ, ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ n (fun x => d1 f x) := by
  have h1 : ContDiff ℝ (n : ℕ∞ω) (fun p : E2 × E2 => (fderiv ℝ f p.1) p.2) :=
    ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := f)
      (n := ((n + 1 : ℕ) : ℕ∞ω)) (m := (n : ℕ∞ω)) (hf (n + 1)) (by push_cast; norm_num)
  have h2 : ContDiff ℝ (n : ℕ∞ω) (fun x : E2 => (fderiv ℝ f x) e1) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  have h3 : (fun x : E2 => d1 f x) = fun x : E2 => (fderiv ℝ f x) e1 := by
    funext x
    exact (hf 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rwa [h3]

theorem tsupport_d0_subset {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    tsupport (fun x : E2 => d0 f x) ⊆ tsupport f := by
  have hfun : (fun x : E2 => d0 f x) = fun x : E2 => fderiv ℝ f x e0 := by
    funext x
    exact (hs 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rw [hfun]
  exact tsupport_fderiv_apply_subset (𝕜 := ℝ) e0

theorem tsupport_d1_subset {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    tsupport (fun x : E2 => d1 f x) ⊆ tsupport f := by
  have hfun : (fun x : E2 => d1 f x) = fun x : E2 => fderiv ℝ f x e1 := by
    funext x
    exact (hs 1).differentiable (by norm_num) x |>.lineDeriv_eq_fderiv
  rw [hfun]
  exact tsupport_fderiv_apply_subset (𝕜 := ℝ) e1

theorem d0_eq_zero_of_notMem_tsupport {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) {x : E2}
    (hx : x ∉ tsupport f) : d0 f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_d0_subset hs h)

theorem d1_eq_zero_of_notMem_tsupport {f : E2 → ℂ} (hs : ∀ n : ℕ, ContDiff ℝ n f) {x : E2}
    (hx : x ∉ tsupport f) : d1 f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_d1_subset hs h)

theorem hasCompactSupport_of_tsupport_subset {f g : E2 → ℂ} (hf : HasCompactSupport f)
    (h : tsupport g ⊆ tsupport f) : HasCompactSupport g :=
  IsCompact.of_isClosed_subset hf (isClosed_tsupport g) h

theorem hasCompactSupport_d0 {f : E2 → ℂ} (hf : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : HasCompactSupport (fun x => d0 f x) :=
  hasCompactSupport_of_tsupport_subset hf (tsupport_d0_subset hs)

theorem hasCompactSupport_d1 {f : E2 → ℂ} (hf : HasCompactSupport f)
    (hs : ∀ n : ℕ, ContDiff ℝ n f) : HasCompactSupport (fun x => d1 f x) :=
  hasCompactSupport_of_tsupport_subset hf (tsupport_d1_subset hs)

theorem contDiff_rho0 {χ tt : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (htts : ∀ n : ℕ, ContDiff ℝ n tt) (n : ℕ) : ContDiff ℝ n (rho0 χ tt) := by
  have h1 := contDiff_d0 (fun k => contDiff_d0 hχs k) n
  have h2 := contDiff_d1 (fun k => contDiff_d1 hχs k) n
  have h3 := contDiff_d0 hχs n
  have h4 := contDiff_d1 hχs n
  exact ((h1.add h2).sub (contDiff_const.mul h3)).add (htts n |>.mul h4)

theorem support_rho0_subset {χ tt : E2 → ℂ} (hχs : ∀ n : ℕ, ContDiff ℝ n χ) :
    Function.support (rho0 χ tt) ⊆ tsupport χ := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxn
  have hd0 : d0 χ x = 0 := d0_eq_zero_of_notMem_tsupport hχs hxn
  have hd1 : d1 χ x = 0 := d1_eq_zero_of_notMem_tsupport hχs hxn
  have htd : tsupport (fun y => d1 χ y) ⊆ tsupport χ := tsupport_d1_subset hχs
  have hd1' : d1 (d1 χ) x = 0 :=
    d1_eq_zero_of_notMem_tsupport (fun k => contDiff_d1 hχs k) (fun h => hxn (htd h))
  have hd0' : d0 (d0 χ) x = 0 :=
    d0_eq_zero_of_notMem_tsupport (fun k => contDiff_d0 hχs k)
      (fun h => hxn ((tsupport_d0_subset hχs) h))
  have hval : rho0 χ tt x = 0 := by
    simp only [rho0, hd0, hd1, hd1', hd0', mul_zero, sub_zero, add_zero]
  exact hx hval

theorem hasCompactSupport_rho0 {χ tt : E2 → ℂ} (hχc : HasCompactSupport χ)
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ) : HasCompactSupport (rho0 χ tt) :=
  hasCompactSupport_of_tsupport_subset hχc (by
    rw [tsupport]
    exact (closure_mono (support_rho0_subset hχs)).trans
      (le_of_eq (isClosed_tsupport χ).closure_eq))

theorem tsupport_mul_subset_left {f g : E2 → ℂ} :
    tsupport (fun x => f x * g x) ⊆ tsupport f := by
  rw [tsupport, tsupport]
  refine closure_mono ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Function.mem_support]
  intro hfx
  exact hx (by rw [hfx, zero_mul])

theorem abs_coord_le_norm (x : E2) (i : Fin 2) : |x i| ≤ ‖x‖ :=
  PiLp.norm_apply_le (p := 2) x i

/-- A point of the ball of radius `δ/2` around `x₀` has its second coordinate strictly inside
`(0, π/2)`, when `δ` measures the distance of `x₀` to the boundary of the strip. -/
theorem mem_Ioo_of_mem_ball {x₀ x : E2} {δ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ x₀ 1)
    (hyδ : δ ≤ Real.pi / 2 - x₀ 1) (hx : x ∈ Metric.ball x₀ (δ / 2)) :
    x 1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hcoord : |x 1 - x₀ 1| ≤ ‖x - x₀‖ := by
    have h := abs_coord_le_norm (x - x₀) 1
    simpa using h
  constructor
  · have h := neg_le_abs (x 1 - x₀ 1)
    linarith
  · have h := le_abs_self (x 1 - x₀ 1)
    linarith

/-- `x ↦ tan (x 1)` is `C^∞` on a ball around `x₀` staying strictly inside the strip
`0 < x 1 < π/2`. -/
theorem contDiffOn_tan_coord {x₀ : E2} {δ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ x₀ 1)
    (hyδ : δ ≤ Real.pi / 2 - x₀ 1) (n : ℕ) :
    ContDiffOn ℝ n (fun x : E2 => (Real.tan (x 1) : ℂ)) (Metric.ball x₀ (δ / 2)) := by
  have htan : ContDiffOn ℝ n (fun y : ℝ => (Real.tan y : ℂ)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro y hy
    have hcos : Real.cos y ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩)
    exact (ContDiffAt.comp y (Complex.ofRealCLM.contDiff.contDiffAt)
      ((Real.contDiffAt_tan).mpr hcos)).contDiffWithinAt
  refine htan.comp ?_ ?_
  · fun_prop
  · intro x hx
    exact mem_Ioo_of_mem_ball hδ hxδ hyδ hx

theorem hasCompactSupport_const_mul {f : E2 → ℂ} (hf : HasCompactSupport f) (c : ℂ) :
    HasCompactSupport (fun x => c * f x) :=
  hasCompactSupport_of_tsupport_subset hf (by
    rw [tsupport, tsupport]
    refine closure_mono ?_
    intro x hx
    rw [Function.mem_support] at hx
    rw [Function.mem_support]
    intro hfx
    exact hx (by rw [hfx, mul_zero]))

end Work.EllipticEst.InteriorRegularity.VT
