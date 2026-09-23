import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

/-- Abstract Taylor–Lagrange cubic remainder bound on `[0,T]`: if `g` and its first three
derivatives exist on `[0,T]` with `g 0 = g' 0 = g'' 0 = 0` and `‖g'''‖ ≤ M`, then
`‖g T‖ ≤ M * T^3 / 6`. Proven by three successive applications of the scalar "fencing"
comparison lemma `image_norm_le_of_norm_deriv_right_le_deriv_boundary`. -/
private theorem taylor_cubic_bound_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' g'' g''' : ℝ → E} {M T : ℝ} (hT : 0 < T)
    (hg0 : g 0 = 0) (hg'0 : g' 0 = 0) (hg''0 : g'' 0 = 0)
    (d1 : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt g (g' t) t)
    (d2 : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt g' (g'' t) t)
    (d3 : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt g'' (g''' t) t)
    (bd : ∀ t ∈ Set.Icc (0:ℝ) T, ‖g''' t‖ ≤ M) :
    ‖g T‖ ≤ M / 6 * T ^ 3 := by
  -- Step 1: `‖g'' t‖ ≤ M * t`.
  have b2 : ∀ t ∈ Set.Icc (0:ℝ) T, ‖g'' t‖ ≤ M * t := by
    have hcont : ContinuousOn g'' (Set.Icc (0:ℝ) T) :=
      fun t ht => (d3 t ht).continuousAt.continuousWithinAt
    have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := g'') (f' := g''') (a := (0:ℝ)) (b := T)
      (B := fun t => M * t) (B' := fun _ => M) hcont
      (fun x hx => (d3 x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (by simp [hg''0])
      (fun x => by simpa using (hasDerivAt_id x).const_mul M)
      (fun x hx => bd x (Set.Ico_subset_Icc_self hx))
    intro t ht
    exact h ht
  -- Step 2: `‖g' t‖ ≤ M/2 * t^2`.
  have b1 : ∀ t ∈ Set.Icc (0:ℝ) T, ‖g' t‖ ≤ M / 2 * t ^ 2 := by
    have hcont : ContinuousOn g' (Set.Icc (0:ℝ) T) :=
      fun t ht => (d2 t ht).continuousAt.continuousWithinAt
    have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => M / 2 * t ^ 2) (M * x) x := by
      intro x
      have h := (hasDerivAt_pow 2 x).const_mul (M / 2)
      refine h.congr_deriv ?_
      simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      ring
    have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := g') (f' := g'') (a := (0:ℝ)) (b := T)
      (B := fun t => M / 2 * t ^ 2) (B' := fun t => M * t) hcont
      (fun x hx => (d2 x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (by simp [hg'0])
      hB
      (fun x hx => b2 x (Set.Ico_subset_Icc_self hx))
    intro t ht
    exact h ht
  -- Step 3: `‖g t‖ ≤ M/6 * t^3`.
  have hcont : ContinuousOn g (Set.Icc (0:ℝ) T) :=
    fun t ht => (d1 t ht).continuousAt.continuousWithinAt
  have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => M / 6 * t ^ 3) (M / 2 * x ^ 2) x := by
    intro x
    have h := (hasDerivAt_pow 3 x).const_mul (M / 6)
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub, Nat.cast_ofNat]
    ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (f' := g') (a := (0:ℝ)) (b := T)
    (B := fun t => M / 6 * t ^ 3) (B' := fun t => M / 2 * t ^ 2) hcont
    (fun x hx => (d1 x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by simp [hg0])
    hB
    (fun x hx => b1 x (Set.Ico_subset_Icc_self hx))
  exact h (Set.right_mem_Icc.mpr (le_of_lt hT))

/-- The cubic Taylor remainder bound for a positive parameter `s`. -/
private theorem taylor_cubic_bound_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' f'' f''' : ℝ → E} {M r s : ℝ} (hs : 0 < s) (hsr : s < r)
    (h1 : ∀ t ∈ Set.Ioo (-r) r, HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Set.Ioo (-r) r, HasDerivAt f' (f'' t) t)
    (h3 : ∀ t ∈ Set.Ioo (-r) r, HasDerivAt f'' (f''' t) t)
    (hbd : ∀ t ∈ Set.Ioo (-r) r, ‖f''' t‖ ≤ M) :
    ‖f s - f 0 - s • f' 0 - (s ^ 2 / 2) • f'' 0‖ ≤ M / 6 * s ^ 3 := by
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) s, t ∈ Set.Ioo (-r) r := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2, hsr]⟩
  have hg0 : (fun t => f t - f 0 - t • f' 0 - (t ^ 2 / 2) • f'' 0) 0 = 0 := by simp
  have hg'0 : (fun t => f' t - f' 0 - t • f'' 0) 0 = 0 := by simp
  have hg''0 : (fun t => f'' t - f'' 0) 0 = 0 := by simp
  have d1 : ∀ t ∈ Set.Icc (0:ℝ) s,
      HasDerivAt (fun u => f u - f 0 - u • f' 0 - (u ^ 2 / 2) • f'' 0)
        (f' t - f' 0 - t • f'' 0) t := by
    intro t ht
    have hmt := hmem t ht
    have hlin : HasDerivAt (fun u : ℝ => u • f' 0) (f' 0) t := by
      simpa using (hasDerivAt_id t).smul_const (f' 0)
    have hquad : HasDerivAt (fun u : ℝ => (u ^ 2 / 2) • f'' 0) (t • f'' 0) t := by
      have h2' : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
        have h := (hasDerivAt_pow 2 t).div_const 2
        refine h.congr_deriv ?_
        simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
        ring
      simpa using h2'.smul_const (f'' 0)
    have hmain := (((h1 t hmt).sub (hasDerivAt_const t (f 0))).sub hlin).sub hquad
    convert hmain using 1
    all_goals first | (funext u; rfl) | simp | rfl
  have d2 : ∀ t ∈ Set.Icc (0:ℝ) s,
      HasDerivAt (fun u => f' u - f' 0 - u • f'' 0) (f'' t - f'' 0) t := by
    intro t ht
    have hmt := hmem t ht
    have hlin : HasDerivAt (fun u : ℝ => u • f'' 0) (f'' 0) t := by
      simpa using (hasDerivAt_id t).smul_const (f'' 0)
    have hmain := ((h2 t hmt).sub (hasDerivAt_const t (f' 0))).sub hlin
    convert hmain using 1
    all_goals first | (funext u; rfl) | simp | rfl
  have d3 : ∀ t ∈ Set.Icc (0:ℝ) s,
      HasDerivAt (fun u => f'' u - f'' 0) (f''' t) t := by
    intro t ht
    have hmt := hmem t ht
    have hmain := (h3 t hmt).sub (hasDerivAt_const t (f'' 0))
    convert hmain using 1
    all_goals first | (funext u; rfl) | simp | rfl
  have bd : ∀ t ∈ Set.Icc (0:ℝ) s, ‖f''' t‖ ≤ M := fun t ht => hbd t (hmem t ht)
  exact taylor_cubic_bound_zero
    (g := fun t => f t - f 0 - t • f' 0 - (t ^ 2 / 2) • f'' 0)
    (g' := fun t => f' t - f' 0 - t • f'' 0)
    (g'' := fun t => f'' t - f'' 0)
    (g''' := f''') (M := M) (T := s) hs hg0 hg'0 hg''0 d1 d2 d3 bd

theorem taylor_second_order_cubic_rem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' f'' f''' : ℝ → E} {M r : ℝ} (hr : 0 < r)
    (h1 : ∀ s ∈ Set.Ioo (-r) r, HasDerivAt f (f' s) s)
    (h2 : ∀ s ∈ Set.Ioo (-r) r, HasDerivAt f' (f'' s) s)
    (h3 : ∀ s ∈ Set.Ioo (-r) r, HasDerivAt f'' (f''' s) s)
    (hbd : ∀ s ∈ Set.Ioo (-r) r, ‖f''' s‖ ≤ M) :
    ∀ s ∈ Set.Ioo (-r) r,
      ‖f s - f 0 - s • f' 0 - (s ^ 2 / 2) • f'' 0‖ ≤ M / 6 * |s| ^ 3 := by
  intro s hs
  rcases lt_or_ge s 0 with hsneg | hsnonneg
  · -- Reflection `t ↦ -t` to reduce to the positive case.
    set F : ℝ → E := fun t => f (-t) with hF
    set F1 : ℝ → E := fun t => - f' (-t) with hF1
    set F2 : ℝ → E := fun t => f'' (-t) with hF2
    set F3 : ℝ → E := fun t => - f''' (-t) with hF3
    have hsymm : ∀ t : ℝ, t ∈ Set.Ioo (-r) r → -t ∈ Set.Ioo (-r) r := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hF1d : ∀ t ∈ Set.Ioo (-r) r, HasDerivAt F (F1 t) t := by
      intro t ht
      have h := HasDerivAt.scomp t (h1 (-t) (hsymm t ht)) (hasDerivAt_neg t)
      simpa [hF, hF1, Function.comp_def, neg_smul] using h
    have hF2d : ∀ t ∈ Set.Ioo (-r) r, HasDerivAt F1 (F2 t) t := by
      intro t ht
      have hg : HasDerivAt (fun u : ℝ => - f' u) (- f'' (-t)) (-t) :=
        (h2 (-t) (hsymm t ht)).neg
      have h := HasDerivAt.scomp t hg (hasDerivAt_neg t)
      simpa [hF1, hF2, Function.comp_def, neg_smul] using h
    have hF3d : ∀ t ∈ Set.Ioo (-r) r, HasDerivAt F2 (F3 t) t := by
      intro t ht
      have h := HasDerivAt.scomp t (h3 (-t) (hsymm t ht)) (hasDerivAt_neg t)
      simpa [hF2, hF3, Function.comp_def, neg_smul] using h
    have hbdd : ∀ t ∈ Set.Ioo (-r) r, ‖F3 t‖ ≤ M := by
      intro t ht
      simpa [hF3] using hbd (-t) (hsymm t ht)
    have hbnd := taylor_cubic_bound_pos (f := F) (f' := F1) (f'' := F2) (f''' := F3)
      (by linarith : (0:ℝ) < -s) (by linarith [hs.1] : -s < r) hF1d hF2d hF3d hbdd
    have hval : F (-s) - F 0 - (-s) • F1 0 - ((-s) ^ 2 / 2) • F2 0
        = f s - f 0 - s • f' 0 - (s ^ 2 / 2) • f'' 0 := by
      have hsmul : (-s) • (- f' 0) = s • (f' 0) := by
        rw [smul_neg, neg_smul, neg_neg]
      have hsq : ((-s) ^ 2) = s ^ 2 := by ring
      simp only [hF, hF1, hF2, neg_neg, neg_zero, hsq, hsmul]
    rw [hval] at hbnd
    rw [abs_of_neg hsneg]
    exact hbnd
  · rcases eq_or_lt_of_le hsnonneg with h | h
    · subst h; simp
    · have hb := taylor_cubic_bound_pos h hs.2 h1 h2 h3 hbd
      rw [abs_of_nonneg hsnonneg]
      exact hb

end Commons.Analysis.Calculus