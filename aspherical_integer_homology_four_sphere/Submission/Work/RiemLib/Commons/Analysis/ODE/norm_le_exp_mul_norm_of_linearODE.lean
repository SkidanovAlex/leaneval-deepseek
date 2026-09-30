import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.RiemLib.Commons.Analysis.ODE.dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set

/-- Reverse-time Grönwall inequality.  If `x` and `y` are differentiable on `[a, b]` with
derivatives `x'` and `y'` satisfying `‖x' t - y' t‖ ≤ L * ‖x t - y t‖`, then the distance at the
left endpoint is bounded by the distance at the right endpoint times `exp (L * (b - a))`.
This is the companion of `dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le`, obtained from it by
reversing time. -/
theorem dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le_reverse
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x y x' y' : ℝ → F} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hx : ∀ t ∈ Set.Icc a b, HasDerivAt x (x' t) t)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (y' t) t)
    (hxy : ∀ t ∈ Set.Icc a b, ‖x' t - y' t‖ ≤ L * ‖x t - y t‖) :
    dist (x a) (y a) ≤ dist (x b) (y b) * Real.exp (L * (b - a)) := by
  have hmem : ∀ u ∈ Set.Icc (0 : ℝ) (b - a), b - u ∈ Set.Icc a b := by
    intro u hu
    rw [Set.mem_Icc] at hu ⊢
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1]⟩
  have hX : ∀ u ∈ Set.Icc (0 : ℝ) (b - a),
      HasDerivAt (fun u => x (b - u)) (-(x' (b - u))) u := by
    intro u hu
    have hg : HasDerivAt (fun u : ℝ => b - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub b
    have h := (hx (b - u) (hmem u hu)).scomp u hg
    rw [Function.comp_def] at h
    simpa using h
  have hY : ∀ u ∈ Set.Icc (0 : ℝ) (b - a),
      HasDerivAt (fun u => y (b - u)) (-(y' (b - u))) u := by
    intro u hu
    have hg : HasDerivAt (fun u : ℝ => b - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub b
    have h := (hy (b - u) (hmem u hu)).scomp u hg
    rw [Function.comp_def] at h
    simpa using h
  have hXY : ∀ u ∈ Set.Icc (0 : ℝ) (b - a),
      ‖-(x' (b - u)) - (-(y' (b - u)))‖ ≤ L * ‖x (b - u) - y (b - u)‖ := by
    intro u hu
    have h1 := hxy (b - u) (hmem u hu)
    have heq : -(x' (b - u)) - (-(y' (b - u))) = -(x' (b - u) - y' (b - u)) := by abel
    rw [heq, norm_neg]
    exact h1
  have h := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le
    (x := fun u => x (b - u)) (y := fun u => y (b - u))
    (x' := fun u => -(x' (b - u))) (y' := fun u => -(y' (b - u)))
    (a := 0) (b := b - a) (L := L) (by linarith) hL hX hY hXY
  simpa only [sub_sub_cancel, sub_zero] using h

/-- **Grönwall estimate for a linear ODE.**  If `z` solves `z' = A · z` at every point of the
interval between `t₀` and `t` and `‖A s‖ ≤ M` for all `s`, then
`‖z t‖ ≤ ‖z t₀‖ * exp (M * |t - t₀|)`. -/
theorem norm_le_exp_mul_norm_of_linearODE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {M : NNReal} (hM : ∀ t, ‖A t‖ ≤ M) {z : ℝ → E} {t₀ t : ℝ}
    (hz : ∀ s ∈ Set.Icc (min t₀ t) (max t₀ t), HasDerivAt z (A s (z s)) s) :
    ‖z t‖ ≤ ‖z t₀‖ * Real.exp ((M : ℝ) * |t - t₀|) := by
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  have h0deriv : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (0 : E)) (0 : E) s :=
    fun s => hasDerivAt_const s 0
  have hbound : ∀ s : ℝ, ‖A s (z s)‖ ≤ (M : ℝ) * ‖z s‖ := by
    intro s
    exact le_trans (ContinuousLinearMap.le_opNorm (A s) (z s))
      (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _))
  have hxy : ∀ s : ℝ, ‖A s (z s) - (0 : E)‖ ≤ (M : ℝ) * ‖z s - (0 : E)‖ := by
    intro s
    simpa using hbound s
  rcases le_total t₀ t with ht | ht
  · have hz' : ∀ s ∈ Set.Icc t₀ t, HasDerivAt z (A s (z s)) s := by
      intro s hs
      exact hz s (by rw [min_eq_left ht, max_eq_right ht]; exact hs)
    have hg := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le
      (x := z) (y := fun _ : ℝ => (0 : E)) (x' := fun s => A s (z s))
      (y' := fun _ : ℝ => (0 : E)) (a := t₀) (b := t) (L := (M : ℝ)) ht hM0 hz'
      (fun s _ => h0deriv s) (fun s hs => hxy s)
    rw [dist_eq_norm, dist_eq_norm] at hg
    simp only [sub_zero] at hg
    rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    exact hg
  · have hz' : ∀ s ∈ Set.Icc t t₀, HasDerivAt z (A s (z s)) s := by
      intro s hs
      exact hz s (by rw [min_eq_right ht, max_eq_left ht]; exact hs)
    have hg := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le_reverse
      (x := z) (y := fun _ : ℝ => (0 : E)) (x' := fun s => A s (z s))
      (y' := fun _ : ℝ => (0 : E)) (a := t) (b := t₀) (L := (M : ℝ)) ht hM0 hz'
      (fun s _ => h0deriv s) (fun s hs => hxy s)
    rw [dist_eq_norm, dist_eq_norm] at hg
    simp only [sub_zero] at hg
    rw [abs_of_nonpos (sub_nonpos.mpr ht), neg_sub]
    exact hg

end Commons.Analysis.ODE