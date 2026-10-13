import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The second derivative of `Real.smoothTransition` vanishes off `(0, 1)`

`Real.smoothTransition` is (infinitely) smooth, equals `0` on `(-∞, 0]` and `1` on `[1, ∞)`.
Consequently its first derivative vanishes on `(-∞, 0)` and on `(1, ∞)`, and so does its second
derivative (the derivative of the first derivative).  Since `deriv (deriv smoothTransition)` is
*continuous* (it is the second derivative of a `C^∞` function), the closed sets `(-∞, 0]` and
`[1, ∞)` are contained in the zero set as well: a closed set containing `(-∞, 0)` contains its
closure `(-∞, 0]`.

The proof is therefore: (i) `deriv smoothTransition = 0` on each open half-line (eventual
constancy), (ii) `deriv (deriv smoothTransition) = 0` on each open half-line, (iii) continuity of
`deriv (deriv smoothTransition)`, (iv) closure.
-/

open scoped Real Topology ContDiff

namespace Work.FTS.EllipticEst.AngAWeak.FluxAux

open Filter

private lemma dpsi_eq_zero_of_lt {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

private lemma dpsi_eq_zero_of_gt {x : ℝ} (hx : 1 < x) : deriv Real.smoothTransition x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) :=
    hmem.mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

private lemma d2psi_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, y < 0 := IsOpen.mem_nhds isOpen_Iio hx
  have heq : (deriv Real.smoothTransition) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => dpsi_eq_zero_of_lt hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

private lemma d2psi_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hmem : ∀ᶠ y in 𝓝 x, 1 < y := IsOpen.mem_nhds isOpen_Ioi hx
  have heq : (deriv Real.smoothTransition) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    hmem.mono fun y hy => dpsi_eq_zero_of_gt hy
  rw [Filter.EventuallyEq.deriv_eq heq, deriv_const]

/-- `deriv (deriv Real.smoothTransition)` is continuous, being the second derivative of a
`C^∞` function. -/
private lemma continuous_d2psi : Continuous (deriv (deriv Real.smoothTransition)) := by
  have hψ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hone : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  exact (hψ.deriv').continuous_deriv hone

theorem deriv2SmoothTransition_flat (t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) :
    deriv (deriv Real.smoothTransition) t = 0 := by
  have hS : IsClosed {x : ℝ | deriv (deriv Real.smoothTransition) x = 0} :=
    isClosed_eq continuous_d2psi continuous_const
  have hleft : Set.Iic (0 : ℝ) ⊆ {x : ℝ | deriv (deriv Real.smoothTransition) x = 0} := by
    rw [← closure_Iio (a := (0 : ℝ))]
    exact hS.closure_subset_iff.mpr (fun y hy => d2psi_eq_zero_of_lt hy)
  have hright : Set.Ici (1 : ℝ) ⊆ {x : ℝ | deriv (deriv Real.smoothTransition) x = 0} := by
    rw [← closure_Ioi (a := (1 : ℝ))]
    exact hS.closure_subset_iff.mpr (fun y hy => d2psi_eq_zero_of_gt hy)
  rcases ht with h | h
  · exact hleft h
  · exact hright h

end Work.FTS.EllipticEst.AngAWeak.FluxAux
