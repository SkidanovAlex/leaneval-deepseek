import Mathlib

/-!
# `3`-Hölder continuity for maps with vanishing first and second derivative

If a smooth map `f : E → F` (with `E`, `F` finite dimensional real normed spaces) has
`fderiv ℝ f x = 0` and `fderiv ℝ (fderiv ℝ f) x = 0`, then on the set
`Z = {z | fderiv ℝ f z = 0 ∧ fderiv ℝ (fderiv ℝ f) z = 0}`, locally around `x`, the map `f` is
`3`-Hölder continuous.

The argument is a three-step Taylor argument, done in a way that never forms the operator norm of
the *third* derivative of `f` (which lives in a triply nested space of continuous linear maps and
whose `NormedAddCommGroup` instance is not synthesizable by typeclass search):

* `T := fderiv ℝ (fderiv ℝ f)` is `C^∞`, hence locally Lipschitz: this is
  `ContDiffOn.exists_lipschitzOnWith` applied on the compact ball `closedBall x 1`.  Note that this
  only mentions norms on `E` and on `E →L[ℝ] (E →L[ℝ] F)`, both of which exist.
* Applying the *one-dimensional* mean value inequality to `t ↦ D (z + t • (w - z))`
  (`D := fderiv ℝ f`) on `[0,1]` gives `‖D w - D z‖ ≤ L ‖w - z‖²` whenever `z ∈ Z` and both points
  lie in the ball: the derivative of that curve at `t` is `(fderiv ℝ D (z+t•v)) v`, which equals
  `((T (z+t•v)) - T z) v` because `T z = 0`, and this is bounded by `‖T (z+t•v) - T z‖ ‖v‖`.
* Applying the same one-dimensional mean value inequality to `t ↦ f (z + t • (w - z))` gives
  `‖f w - f z‖ ≤ L ‖w - z‖³`.

Taking `t := Z ∩ K ∩ closedBall x 1` finishes the proof.
-/

namespace Work.Sard

/-- A cubic norm bound on a set upgrades to `HolderOnWith` with exponent `3`. -/
lemma holderOnWith_three_of_norm_sub_le {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {f : E → F} {t : Set E} {C : NNReal}
    (h : ∀ x ∈ t, ∀ y ∈ t, ‖f x - f y‖ ≤ (C : ℝ) * ‖x - y‖ ^ (3 : ℝ)) :
    HolderOnWith C 3 f t := by
  intro x hx y hy
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← ENNReal.ofReal_coe_nnreal]
  rw [show ((3 : NNReal) : ℝ) = 3 from by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.ofReal_mul (C.coe_nonneg)]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- **`3`-Hölder estimate for maps with vanishing first and second derivative.**  A smooth map with
`fderiv ℝ f x = 0` and `fderiv ℝ (fderiv ℝ f) x = 0` is, locally on that set, Hölder continuous with
exponent `3`.

Proof sketch (direct Taylor, not a recursion on the `2`-Hölder estimate): let
`Z := {z : E | fderiv ℝ f z = 0 ∧ fderiv ℝ (fun y => fderiv ℝ f y) z = 0}`.  `f'''` (i.e.
`fderiv ℝ (fun y => fderiv ℝ (fun y => fderiv ℝ f y) y)`) is continuous at `x`, so bounded by `M` on a
ball `closedBall x r`; take `t := Z ∩ K ∩ closedBall x r`.  For `z ∈ t` the second-order Taylor formula
with base point `z` (Mathlib has `TaylorIsLittleO`/`taylor_isLittleO` style results, or argue with the
convex mean value inequality applied twice to `fderiv ℝ f - 0`) gives
`‖f y - f z‖ ≤ M * ‖y - z‖ ^ 3` for `y ∈ closedBall z r'`, and for `y, y' ∈ t` one may take the base point
to be either of them, so it suffices that the estimate holds with a uniform constant on the ball; use
`‖y - y'‖ ≤ 2 * r`-type bounds.  Then `HolderOnWith M 3 f t` and `t ∈ nhdsWithin x (Z ∩ K)`. -/
theorem holder_three_snd_fderiv_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set E) :
    ∀ x ∈ {x : E | fderiv ℝ f x = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0} ∩ K,
      ∃ C : NNReal,
        ∃ t ∈ nhdsWithin x
            ({x : E | fderiv ℝ f x = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) x = 0} ∩ K),
          HolderOnWith C 3 f t := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
  obtain ⟨⟨hx1, hx2⟩, _hxK⟩ := hx
  let D : E → E →L[ℝ] F := fderiv ℝ f
  let T : E → E →L[ℝ] (E →L[ℝ] F) := fderiv ℝ D
  have hDc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D := hf.fderiv_right le_rfl
  have hTc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T := hDc.fderiv_right le_rfl
  have hDdiff : ∀ w : E, DifferentiableAt ℝ D w :=
    fun w => (hDc.differentiable (by simp)).differentiableAt
  have hfdiff : ∀ w : E, DifferentiableAt ℝ f w :=
    fun w => (hf.differentiable (by simp)).differentiableAt
  -- `T` is locally Lipschitz: it is `C^1`, and we work on the compact ball `closedBall x 1`.
  obtain ⟨C₀, hC₀⟩ : ∃ C : NNReal, LipschitzOnWith C T (Metric.closedBall x 1) :=
    (hTc.contDiffOn.mono (Set.subset_univ _)).exists_lipschitzOnWith (by simp)
      (convex_closedBall x 1) (isCompact_closedBall x 1)
  -- second order estimate for `D = fderiv ℝ f`
  have hDq : ∀ z ∈ Metric.closedBall x 1, D z = 0 → T z = 0 → ∀ w ∈ Metric.closedBall x 1,
      ‖D w‖ ≤ (C₀ : ℝ) * ‖w - z‖ ^ 2 := by
    intro z hzB hzD hzT w hwB
    set v : E := w - z with hv
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => D (z + t • v)) ((T (z + t • v)) v) t := by
      intro t ht
      have hφ : HasDerivAt (fun t : ℝ => z + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add z
      exact ((hDdiff (z + t • v)).hasFDerivAt).comp_hasDerivAt t hφ
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(T (z + t • v)) v‖ ≤ (C₀ : ℝ) * ‖v‖ ^ 2 := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have hmem : z + t • v ∈ Metric.closedBall x 1 := by
        rw [hv]
        exact (convex_closedBall x 1).add_smul_mem hzB (by simpa using hwB) ht
      have h1 : ‖T (z + t • v) - T z‖ ≤ (C₀ : ℝ) * ‖z + t • v - z‖ := hC₀.norm_sub_le hmem hzB
      have h2 : ‖z + t • v - z‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      calc ‖(T (z + t • v)) v‖ = ‖(T (z + t • v) - T z) v‖ := by
            rw [sub_apply, hzT, zero_apply, sub_zero]
        _ ≤ ‖T (z + t • v) - T z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((C₀ : ℝ) * ‖z + t • v - z‖) * ‖v‖ := by gcongr
        _ = (C₀ : ℝ) * t * ‖v‖ ^ 2 := by rw [h2]; ring
        _ ≤ (C₀ : ℝ) * 1 * ‖v‖ ^ 2 := by gcongr; exact ht.2
        _ = (C₀ : ℝ) * ‖v‖ ^ 2 := by ring
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t : ℝ => D (z + t • v))
      (f' := fun t : ℝ => (T (z + t • v)) v) (C := (C₀ : ℝ) * ‖v‖ ^ 2)
      (fun t ht => (hderiv t ht).hasDerivWithinAt)
      (fun t ht => hbound t (Set.Ico_subset_Icc_self ht))
    have hmain' : ‖D w - D z‖ ≤ (C₀ : ℝ) * ‖v‖ ^ 2 := by simpa [hv] using hmain
    rw [hzD, sub_zero] at hmain'
    exact hmain'
  -- third order estimate for `f`
  have hcub : ∀ z ∈ Metric.closedBall x 1, D z = 0 → T z = 0 → ∀ y ∈ Metric.closedBall x 1,
      ‖f y - f z‖ ≤ (C₀ : ℝ) * ‖y - z‖ ^ 3 := by
    intro z hzB hzD hzT y hyB
    set v : E := y - z with hv
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => f (z + t • v)) ((D (z + t • v)) v) t := by
      intro t ht
      have hφ : HasDerivAt (fun t : ℝ => z + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add z
      exact ((hfdiff (z + t • v)).hasFDerivAt).comp_hasDerivAt t hφ
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(D (z + t • v)) v‖ ≤ (C₀ : ℝ) * ‖v‖ ^ 3 := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have hmem : z + t • v ∈ Metric.closedBall x 1 := by
        rw [hv]
        exact (convex_closedBall x 1).add_smul_mem hzB (by simpa using hyB) ht
      have h1 : ‖D (z + t • v)‖ ≤ (C₀ : ℝ) * ‖z + t • v - z‖ ^ 2 :=
        hDq z hzB hzD hzT (z + t • v) hmem
      have h2 : ‖z + t • v - z‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht.2
      calc ‖(D (z + t • v)) v‖ ≤ ‖D (z + t • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((C₀ : ℝ) * ‖z + t • v - z‖ ^ 2) * ‖v‖ := by gcongr
        _ = (C₀ : ℝ) * t ^ 2 * ‖v‖ ^ 3 := by rw [h2]; ring
        _ ≤ (C₀ : ℝ) * 1 * ‖v‖ ^ 3 := by gcongr
        _ = (C₀ : ℝ) * ‖v‖ ^ 3 := by ring
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t : ℝ => f (z + t • v))
      (f' := fun t : ℝ => (D (z + t • v)) v) (C := (C₀ : ℝ) * ‖v‖ ^ 3)
      (fun t ht => (hderiv t ht).hasDerivWithinAt)
      (fun t ht => hbound t (Set.Ico_subset_Icc_self ht))
    simpa [hv] using hmain
  refine ⟨C₀, ({z : E | fderiv ℝ f z = 0 ∧ fderiv ℝ (fun y : E => fderiv ℝ f y) z = 0} ∩ K)
      ∩ Metric.closedBall x 1, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds x (by norm_num))
  · refine holderOnWith_three_of_norm_sub_le (C := C₀) ?_
    intro y hy y' hy'
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hy hy'
    have h := hcub y' hy'.2 hy'.1.1.1 hy'.1.1.2 y hy.2
    simpa using h

end Work.Sard
