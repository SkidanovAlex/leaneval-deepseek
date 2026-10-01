import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Submission.Commons.Analysis.Calculus.norm_le_mul_sq_of_iteratedDeriv_two_le

open Set

namespace Commons.Analysis.Calculus

/-- If `f` is continuous on `[0, ∞)`, vanishes for `t ≥ x₀`, and is `C²` on `(0, x₀)` with
`‖f''‖ ≤ B` there, then for every `t ∈ (0, x₀)` one has
`|f' t| ≤ B * x₀ + |f 0| / x₀`.

The proof subtracts the chord `s ↦ (f 0 / x₀) * (x₀ - s)` from `f`, which annihilates the
boundary values at `0` and `x₀`, so that the auxiliary function `h` satisfies `h 0 = h x₀ = 0`,
`h'' = f''` and `h' = f' + f 0 / x₀`. The commons lemma
`norm_le_mul_sq_of_iteratedDeriv_two_le` then bounds `|h'|` by `B * x₀`. -/
theorem abs_deriv_le_of_iteratedDeriv_two_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∀ t ∈ Set.Ioo (0:ℝ) x₀, |deriv f t| ≤ B * x₀ + |f 0| / x₀ := by
  intro t ht
  have hx0 : f x₀ = 0 := hsupp x₀ le_rfl
  have hx₀ne : x₀ ≠ 0 := ne_of_gt hx₀
  set c : ℝ := f 0 / x₀ with hcdef
  let h : ℝ → ℝ := fun s => f s + (c * s - f 0)
  have hcx : c * x₀ - f 0 = 0 := by rw [hcdef, div_mul_cancel₀ (f 0) hx₀ne]; ring
  have hh0 : h 0 = 0 := by simp [h]
  have hhx : h x₀ = 0 := by simp only [h]; rw [hx0, hcx]; ring
  have hcont_h : ContinuousOn h (Set.Icc (0:ℝ) x₀) := by
    apply ContinuousOn.add
    · exact hcont.mono (Set.Icc_subset_Ici_self)
    · fun_prop
  have hf2_h : ContDiffOn ℝ 2 h (Set.Ioo (0:ℝ) x₀) := by
    apply ContDiffOn.add
    · exact hf2
    · fun_prop
  have hzero : ∀ u, iteratedDeriv 2 (fun s : ℝ => c * s - f 0) u = 0 := by
    intro u
    rw [iteratedDeriv_fun_sub]
    · rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_id, iteratedDeriv_const]
      norm_num
    · fun_prop
    · fun_prop
  have hBnd_h : ∀ s ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 h s‖ ≤ B := by
    intro s hs
    have hiter : iteratedDeriv 2 h s = iteratedDeriv 2 f s := by
      rw [show h = fun s => f s + (c * s - f 0) from rfl]
      rw [iteratedDeriv_fun_add]
      · rw [hzero s, add_zero]
      · exact hf2.contDiffAt (isOpen_Ioo.mem_nhds hs)
      · fun_prop
    rw [hiter]
    exact hBnd s hs
  obtain ⟨_, hderivbound⟩ :=
    Commons.Analysis.Calculus.norm_le_mul_sq_of_iteratedDeriv_two_le
      hx₀ hcont_h hf2_h hBnd_h hh0 hhx
  have hdh : deriv h t = deriv f t + c := by
    have ht2 : ContDiffAt ℝ 2 f t := hf2.contDiffAt (isOpen_Ioo.mem_nhds ht)
    have hdf : DifferentiableAt ℝ f t := ht2.differentiableAt (by norm_num)
    have hde : DifferentiableAt ℝ (fun s : ℝ => c * s - f 0) t := by fun_prop
    have heq : h = (fun s : ℝ => f s) + (fun s : ℝ => c * s - f 0) := by
      funext s; simp [h, Pi.add_apply]
    rw [heq, deriv_add hdf hde, deriv_sub_const (f 0), deriv_const_mul_id c]
  have h1 : ‖deriv h t‖ ≤ B * x₀ := hderivbound t ht
  rw [hdh, Real.norm_eq_abs] at h1
  calc |deriv f t| = |(deriv f t + c) - c| := by congr 1; ring
    _ ≤ |deriv f t + c| + |c| := by simpa using abs_add_le (deriv f t + c) (-c)
    _ ≤ B * x₀ + |c| := by linarith
    _ = B * x₀ + |f 0| / x₀ := by rw [hcdef, abs_div, abs_of_pos hx₀]

end Commons.Analysis.Calculus