/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular cut-off `χ` of the weak slice estimate

`χ θ = smoothTransition (2 - 8θ/π)` is `1` on `(-∞, π/8]` and `0` on `[π/4, ∞)`; it is used to
remove the (possibly non-zero) limit `L = lim_{0⁺} u` of a slice of the weak class before the
integration-by-parts identity `sliceIdGlobal` is applied.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The smooth cut-off `χ θ = smoothTransition (2 - 8θ/π)`: it equals `1` on `(-∞, π/8]` and
`0` on `[π/4, ∞)`. -/
def chiAng (θ : ℝ) : ℝ := Real.smoothTransition (2 - 8 * θ / Real.pi)

lemma chiAng_eq_one {θ : ℝ} (h : θ ≤ Real.pi / 8) : chiAng θ = 1 := by
  unfold chiAng
  refine Real.smoothTransition.one_of_one_le ?_
  have hpi := Real.pi_pos
  have h2 : 8 * θ / Real.pi ≤ 1 := by rw [div_le_one hpi]; linarith
  linarith

lemma chiAng_eq_zero {θ : ℝ} (h : Real.pi / 4 ≤ θ) : chiAng θ = 0 := by
  unfold chiAng
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hpi := Real.pi_pos
  have h2 : 2 ≤ 8 * θ / Real.pi := by rw [le_div_iff₀ hpi]; linarith
  linarith

lemma chiAng_nonneg (θ : ℝ) : 0 ≤ chiAng θ := by
  unfold chiAng; exact Real.smoothTransition.nonneg _

lemma chiAng_le_one (θ : ℝ) : chiAng θ ≤ 1 := by
  unfold chiAng; exact Real.smoothTransition.le_one _

lemma chiAng_contDiff (n : ℕ) : ContDiff ℝ n chiAng := by
  unfold chiAng
  have h1 : ContDiff ℝ n (fun θ : ℝ => 2 - 8 * θ / Real.pi) := by fun_prop
  exact (Real.smoothTransition.contDiff (n := n)).comp h1

lemma chiAng_contDiffOn (n : ℕ) :
    ContDiffOn ℝ n chiAng (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (chiAng_contDiff n).contDiffOn

/-- On `(-∞, π/8)` the cut-off is identically `1`. -/
lemma chiAng_eventuallyEq_one {θ : ℝ} (hθ : θ < Real.pi / 8) :
    chiAng =ᶠ[𝓝 θ] fun _ => (1 : ℝ) :=
  Filter.eventuallyEq_of_mem (isOpen_Iio.mem_nhds hθ) fun _ ht => chiAng_eq_one ht.le

/-- On `(π/4, ∞)` the cut-off is identically `0`. -/
lemma chiAng_eventuallyEq_zero {θ : ℝ} (hθ : Real.pi / 4 < θ) :
    chiAng =ᶠ[𝓝 θ] fun _ => (0 : ℝ) :=
  Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hθ) fun _ ht => chiAng_eq_zero ht.le

lemma deriv_chiAng_eq_zero_of_lt {θ : ℝ} (hθ : θ < Real.pi / 8) : deriv chiAng θ = 0 := by
  rw [(chiAng_eventuallyEq_one hθ).deriv_eq]; simp

lemma deriv_chiAng_eq_zero_of_gt {θ : ℝ} (hθ : Real.pi / 4 < θ) : deriv chiAng θ = 0 := by
  rw [(chiAng_eventuallyEq_zero hθ).deriv_eq]; simp

/-- The cut-off is locally constant near `0`, so all its derivatives vanish on `(0, π/8)`. -/
lemma deriv_chiAng_eq_zero_of_lt' {θ : ℝ} (hθ : θ < Real.pi / 8) :
    deriv (deriv chiAng) θ = 0 := by
  have h1 : deriv chiAng =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    have h := (chiAng_eventuallyEq_one hθ).deriv
    simpa using h
  rw [Filter.EventuallyEq.deriv_eq h1]
  simp

/-- The cut-off is locally constant near points of `(π/4, π/2)`, so all its derivatives vanish
there. -/
lemma deriv_chiAng_eq_zero_of_gt' {θ : ℝ} (hθ : Real.pi / 4 < θ) :
    deriv (deriv chiAng) θ = 0 := by
  have h1 : deriv chiAng =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    have h := (chiAng_eventuallyEq_zero hθ).deriv
    simpa using h
  rw [Filter.EventuallyEq.deriv_eq h1]
  simp

/-- Eventually (in `𝓝[>] 0`) the cut-off equals `1`. -/
lemma eventually_chiAng_eq_one : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), chiAng θ = 1 := by
  have hmem : Set.Ioo (-1 : ℝ) (Real.pi / 8) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by linarith [Real.pi_pos])
  filter_upwards [nhdsWithin_le_nhds hmem] with θ hθ
  exact chiAng_eq_one hθ.2.le

/-- Eventually (in `𝓝[<] (π/2)`) the cut-off equals `0`. -/
lemma eventually_chiAng_eq_zero : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
    chiAng θ = 0 := by
  have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2 + 1) ∈ 𝓝 (Real.pi / 2) :=
    Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  filter_upwards [nhdsWithin_le_nhds hmem] with θ hθ
  exact chiAng_eq_zero hθ.1.le

/-- The corrected slice `t = u - L·χ`. -/
def corrSlice (u : ℝ → ℝ) (L : ℝ) : ℝ → ℝ := fun θ => u θ - L * chiAng θ

lemma corrSlice_contDiffOn {u : ℝ → ℝ} {L : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0:ℝ) (Real.pi/2))) :
    ContDiffOn ℝ 2 (corrSlice u L) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  unfold corrSlice
  exact hu.sub (contDiffOn_const.mul (chiAng_contDiffOn 2))

lemma Lzero1_corrSlice {u : ℝ → ℝ} {L : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0:ℝ) (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Lzero1 (corrSlice u L) θ = Lzero1 u θ - L * Lzero1 chiAng θ := by
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hc : ContDiffOn ℝ 2 chiAng (Set.Ioo (0:ℝ) (Real.pi/2)) := chiAng_contDiffOn 2
  -- the first derivative identity, wherever we are in the open interval
  have hderiv1 : ∀ s ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      deriv (corrSlice u L) s = deriv u s - L * deriv chiAng s := by
    intro s hs
    have hu_d : DifferentiableAt ℝ u s :=
      (hu.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hs)
    have hc_d : DifferentiableAt ℝ chiAng s :=
      (hc.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hs)
    have hh : HasDerivAt (fun t => u t - L * chiAng t) (deriv u s - L * deriv chiAng s) s :=
      (hu_d.hasDerivAt).sub ((hc_d.hasDerivAt).const_mul L)
    exact hh.deriv
  have hu_d : DifferentiableAt ℝ u θ :=
    (hu.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hθ)
  have hc_d : DifferentiableAt ℝ chiAng θ :=
    (hc.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hθ)
  have hdu_d : DifferentiableAt ℝ (deriv u) θ := by
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hu.deriv_of_isOpen hIoo (by norm_num)
    exact (h1.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hθ)
  have hdc_d : DifferentiableAt ℝ (deriv chiAng) θ := by
    have h1 : ContDiffOn ℝ 1 (deriv chiAng) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hc.deriv_of_isOpen hIoo (by norm_num)
    exact (h1.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hθ)
  have hcos : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne'
  have htanu_d : DifferentiableAt ℝ (fun s => Real.tan s * u s) θ :=
    (Real.differentiableAt_tan.2 hcos).mul hu_d
  have htanc_d : DifferentiableAt ℝ (fun s => Real.tan s * chiAng s) θ :=
    (Real.differentiableAt_tan.2 hcos).mul hc_d
  have h1 : deriv (corrSlice u L) θ = deriv u θ - L * deriv chiAng θ := hderiv1 θ hθ
  have h2 : deriv (fun s => deriv (corrSlice u L) s) θ
      = deriv (deriv u) θ - L * deriv (deriv chiAng) θ := by
    have hev : deriv (corrSlice u L) =ᶠ[𝓝 θ] fun s => deriv u s - L * deriv chiAng s := by
      filter_upwards [hIoo.mem_nhds hθ] with s hs
      exact hderiv1 s hs
    have hh : HasDerivAt (fun s => deriv u s - L * deriv chiAng s)
        (deriv (deriv u) θ - L * deriv (deriv chiAng) θ) θ :=
      (hdu_d.hasDerivAt).sub ((hdc_d.hasDerivAt).const_mul L)
    rw [hev.deriv_eq]
    exact hh.deriv
  have h3 : deriv (fun s => Real.tan s * corrSlice u L s) θ
      = deriv (fun s => Real.tan s * u s) θ - L * deriv (fun s => Real.tan s * chiAng s) θ := by
    have hev : (fun s => Real.tan s * corrSlice u L s)
        =ᶠ[𝓝 θ] fun s => Real.tan s * u s - L * (Real.tan s * chiAng s) := by
      filter_upwards with s
      simp only [corrSlice]
      ring
    have hsub : deriv ((fun s => Real.tan s * u s) - fun s => L * (Real.tan s * chiAng s)) θ
        = deriv (fun s => Real.tan s * u s) θ
          - deriv (fun s => L * (Real.tan s * chiAng s)) θ :=
      deriv_sub htanu_d (htanc_d.const_mul L)
    have hcm : deriv (fun s => L * (Real.tan s * chiAng s)) θ
        = L * deriv (fun s => Real.tan s * chiAng s) θ := deriv_const_mul L htanc_d
    rw [hev.deriv_eq]
    change deriv ((fun s => Real.tan s * u s) - fun s => L * (Real.tan s * chiAng s)) θ
      = deriv (fun s => Real.tan s * u s) θ - L * deriv (fun s => Real.tan s * chiAng s) θ
    rw [hsub, hcm]
  unfold Lzero1
  rw [h2, h3]
  unfold corrSlice
  ring


/-- The derivative of the corrected slice. -/
lemma deriv_corrSlice {u : ℝ → ℝ} {L : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0:ℝ) (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    deriv (corrSlice u L) θ = deriv u θ - L * deriv chiAng θ := by
  have hIoo : IsOpen (Set.Ioo (0:ℝ) (Real.pi/2)) := isOpen_Ioo
  have hc : ContDiffOn ℝ 2 chiAng (Set.Ioo (0:ℝ) (Real.pi/2)) := chiAng_contDiffOn 2
  have hu_d : DifferentiableAt ℝ u θ :=
    (hu.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hθ)
  have hc_d : DifferentiableAt ℝ chiAng θ :=
    (hc.differentiableOn (by norm_num)).differentiableAt (hIoo.mem_nhds hθ)
  have hh : HasDerivAt (fun t => u t - L * chiAng t) (deriv u θ - L * deriv chiAng θ) θ :=
    (hu_d.hasDerivAt).sub ((hc_d.hasDerivAt).const_mul L)
  exact hh.deriv

end Work.FTS.EllipticEst.AngAWeak
