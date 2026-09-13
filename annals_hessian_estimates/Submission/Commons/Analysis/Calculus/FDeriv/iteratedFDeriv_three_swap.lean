import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Order.CompletePartialOrder

open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

/-- For a `C^3` function on an open set, the third iterated derivative is symmetric in its
first two arguments and in its last two arguments. -/
theorem iteratedFDeriv_three_swap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → F} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ 3 f s) (a b c : E) :
    iteratedFDeriv ℝ 3 f x ![a, b, c] = iteratedFDeriv ℝ 3 f x ![b, a, c] ∧
      iteratedFDeriv ℝ 3 f x ![a, b, c] = iteratedFDeriv ℝ 3 f x ![a, c, b] := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have hfAt : ContDiffAt ℝ 3 f x := hf.contDiffAt hxmem
  -- Express the third derivative through the second derivative of the first derivative.
  have hmain : ∀ u v w : E, iteratedFDeriv ℝ 3 f x ![u, v, w]
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w := by
    intro u v w
    rw [iteratedFDeriv_succ_apply_right (n := 2) (m := ![u, v, w]), iteratedFDeriv_two_apply]
    simp [Fin.init]
  -- The second derivative of `fderiv ℝ f` is symmetric since `fderiv ℝ f` is `C^2`.
  have hsym2 : IsSymmSndFDerivAt ℝ (fderiv ℝ f) x :=
    (hfAt.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num)
  have hab : iteratedFDeriv ℝ 3 f x ![a, b, c] = iteratedFDeriv ℝ 3 f x ![b, a, c] := by
    rw [hmain a b c, hmain b a c, hsym2 a b]
  -- For the swap of the last two arguments, use that the second derivative is symmetric at every
  -- point of `s` and differentiate the resulting identity.
  have hD2diff : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
    (hfAt.iteratedFDeriv_right (i := 2) (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hEq : (fun y => (iteratedFDeriv ℝ 2 f y) ![b, c]) =ᶠ[𝓝 x]
      (fun y => (iteratedFDeriv ℝ 2 f y) ![c, b]) := by
    apply Filter.eventually_of_mem hxmem
    intro y hy
    exact IsSymmSndFDerivAt.iteratedFDeriv_cons (𝕜 := ℝ) (f := f) (x := y)
      (hf := (hf.contDiffAt (hs.mem_nhds hy)).isSymmSndFDerivAt (by norm_num))
  have h1 : iteratedFDeriv ℝ 3 f x ![a, b, c]
      = (fderiv ℝ (iteratedFDeriv ℝ 2 f) x a) ![b, c] := by
    rw [iteratedFDeriv_succ_apply_left (n := 2) (m := ![a, b, c])]
    simp
  have h2 : iteratedFDeriv ℝ 3 f x ![a, c, b]
      = (fderiv ℝ (iteratedFDeriv ℝ 2 f) x a) ![c, b] := by
    rw [iteratedFDeriv_succ_apply_left (n := 2) (m := ![a, c, b])]
    simp
  have hbc : iteratedFDeriv ℝ 3 f x ![a, b, c] = iteratedFDeriv ℝ 3 f x ![a, c, b] := by
    rw [h1, h2, ← fderiv_continuousMultilinear_apply_const_apply (𝕜 := ℝ)
        (c := iteratedFDeriv ℝ 2 f) (M := fun _ : Fin 2 => E) (H := F) hD2diff ![b, c] a,
      ← fderiv_continuousMultilinear_apply_const_apply (𝕜 := ℝ)
        (c := iteratedFDeriv ℝ 2 f) (M := fun _ : Fin 2 => E) (H := F) hD2diff ![c, b] a,
      Filter.EventuallyEq.fderiv_eq hEq]
  exact ⟨hab, hbc⟩

end Commons.Analysis.Calculus.FDeriv