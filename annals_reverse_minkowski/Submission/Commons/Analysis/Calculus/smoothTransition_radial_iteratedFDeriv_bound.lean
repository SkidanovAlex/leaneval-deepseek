import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Derivative bounds for a rescaled radial smooth-transition cutoff

We prove that for every `a : ℕ` there is a single constant `C > 0` such that for every dimension
`d`, every `c > 0` and every `x : ℝᵈ`

`‖D^a (y ↦ smoothTransition (c * ‖y‖ - 1)) x‖ ≤ C * c ^ a`.

Note that the constant `C` is *uniform in the dimension* `d`.  This is the key point: the naive
approach (Faà di Bruno applied to `φ ∘ ‖·‖` on the annulus `1/2 < ‖·‖ < 3`) produces a constant
depending on `d`, because the derivatives of the norm are bounded via compactness of the unit
sphere.  Instead we apply Faà di Bruno to the composition

`y ↦ φ (‖y‖ - 1) = g (‖y‖ ^ 2)`,   `g u = φ (√u - 1)`,

i.e. we use the **squared** norm `q y = ‖y‖ ^ 2` as inner function.  Its iterated derivatives are
explicitly bounded, uniformly in the ambient inner product space `E`: writing `q y = (innerSL ℝ y) y`
as the diagonal of the continuous bilinear inner product and applying the general bound
`norm_iteratedFDeriv_clm_apply`, only the case `q = 0` and `q = 1` derivatives contribute.  The
outer function `g` is smooth on `(0,∞)`, and constant (`= 1`) for `u ≥ 4`, so its derivatives are
bounded on the compact interval `[1/4, 9]` that contains `‖y‖ ^ 2` for `1/2 ≤ ‖y‖ ≤ 3`.

The remaining regions are handled separately: `y ↦ φ(‖y‖ - 1)` vanishes near every point of `‖x‖ < 1`
and equals `1` near every point of `‖x‖ > 2`, so its derivatives vanish there.

Finally the scaling `φ (c ‖x‖ - 1) = F (c • x)` with `F y = φ (‖y‖ - 1)` and
`iteratedFDeriv_comp_const_smul` produce the factor `c ^ a`.
-/

namespace Commons.Analysis.Calculus

open scoped Topology ContDiff
open Set Metric Filter

/-- For `n ≥ 2` the `n`-th iterated derivative of a continuous linear map vanishes: a continuous
linear map is affine, so its derivative is constant. -/
lemma smoothTransition_radial_clm_iteratedFDeriv_eq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ∀ n, 2 ≤ n → iteratedFDeriv ℝ n (⇑L) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hright : iteratedFDeriv ℝ (m + 1) (⇑L)
      = fun x => (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
          (iteratedFDeriv ℝ m (fun y => fderiv ℝ (⇑L) y) x) := by
    funext x
    exact iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := ⇑L) (x := x) (n := m)
  have hfderiv : (fun y : E => fderiv ℝ (⇑L) y) = fun _ => L := by
    funext y
    exact ContinuousLinearMap.fderiv L
  rw [hright, hfderiv, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (n := m) (by omega) L]
  ext x
  simp

/-- Uniform bound for the iterated derivatives of a continuous linear map: only the values `n = 0`
and `n = 1` contribute. -/
lemma smoothTransition_radial_clm_iteratedFDeriv_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (⇑L) x‖ ≤ max ‖L‖ 1 * max ‖x‖ 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := ContinuousLinearMap.le_opNorm L x
      _ ≤ max ‖L‖ 1 * max ‖x‖ 1 := by
          apply mul_le_mul
          · exact le_max_left _ _
          · exact le_max_left _ _
          · exact norm_nonneg x
          · exact le_trans (norm_nonneg L) (le_max_left _ _)
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · have h1 : n = 1 := by omega
      subst h1
      rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
      calc ‖L‖ ≤ max ‖L‖ 1 * 1 := by rw [mul_one]; exact le_max_left _ _
        _ ≤ max ‖L‖ 1 * max ‖x‖ 1 := by
            exact mul_le_mul_of_nonneg_left (le_max_right _ _)
              (le_trans (norm_nonneg L) (le_max_left _ _))
    · simp only [smoothTransition_radial_clm_iteratedFDeriv_eq_zero L n h2, Pi.zero_apply,
        norm_zero]
      positivity

/-- Bound for the iterated derivatives of the squared norm `y ↦ ‖y‖ ^ 2`, uniform in the ambient
inner product space.  For `‖x‖ < 3` and `1 ≤ n` the bound `18 ^ n` holds.

Proof: write `‖y‖ ^ 2 = (innerSL ℝ y) y` and apply the general Leibniz bound
`norm_iteratedFDeriv_clm_apply`.  The factors are bounded by `3` since `‖innerSL ℝ‖ ≤ 1`,
`‖id‖ ≤ 1` and `‖x‖ < 3`, and `∑ i ∈ range (n+1), n.choose i = 2 ^ n`. -/
lemma smoothTransition_radial_norm_sq_iteratedFDeriv_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) (hn : 1 ≤ n) (x : E) (hx : ‖x‖ < 3) :
    ‖iteratedFDeriv ℝ n (fun x : E => ‖x‖ ^ 2) x‖ ≤ 18 ^ n := by
  have hf : ContDiff ℝ ∞ (fun y : E => innerSL ℝ y) :=
    ContinuousLinearMap.contDiff (n := ∞) (innerSL ℝ (E := E))
  have hg : ContDiff ℝ ∞ (id : E → E) := contDiff_id
  have hfun : (fun y : E => (innerSL ℝ y) y) = fun y : E => ‖y‖ ^ 2 := by
    funext y
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have key := norm_iteratedFDeriv_clm_apply (𝕜 := ℝ) (f := fun y : E => innerSL ℝ y)
    (g := (id : E → E)) hf hg x (N := ∞) (n := n)
    (show ((n : ℕ∞) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  simp only [id_eq] at key
  rw [hfun] at key
  have hf_bound : ∀ i, ‖iteratedFDeriv ℝ i (fun y : E => innerSL ℝ y) x‖ ≤ 3 := by
    intro i
    have h := smoothTransition_radial_clm_iteratedFDeriv_le (innerSL ℝ (E := E)) i x
    rw [max_eq_right (norm_innerSL_le ℝ (E := E)), one_mul] at h
    exact h.trans (max_le hx.le (by norm_num))
  have hg_bound : ∀ j, ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 3 := by
    intro j
    have h := smoothTransition_radial_clm_iteratedFDeriv_le (ContinuousLinearMap.id ℝ E) j x
    rw [max_eq_right (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)), one_mul] at h
    exact h.trans (max_le hx.le (by norm_num))
  have hterm : ∀ i : ℕ, (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun y : E => innerSL ℝ y) x‖
        * ‖iteratedFDeriv ℝ (n - i) (id : E → E) x‖ ≤ (n.choose i : ℝ) * 3 * 3 := by
    intro i
    have hci : (0:ℝ) ≤ (n.choose i : ℝ) := by positivity
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hf_bound i) hci) (hg_bound (n-i))
      (norm_nonneg _) (by positivity)
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun y : E => innerSL ℝ y) x‖
        * ‖iteratedFDeriv ℝ (n - i) (id : E → E) x‖ ≤ 9 * 2 ^ n := by
    refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
    have h2 : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * 3 * 3
        = 9 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2]
    have h3 : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
      norm_num
    rw [h3]
  refine key.trans (hsum.trans ?_)
  have h9 : (9:ℝ) ≤ 9 ^ n := by
    calc (9:ℝ) = 9 ^ 1 := (pow_one 9).symm
      _ ≤ 9 ^ n := pow_le_pow_right₀ (by norm_num) hn
  calc (9:ℝ) * 2 ^ n = 2 ^ n * 9 := by ring
    _ ≤ 2 ^ n * 9 ^ n := mul_le_mul_of_nonneg_left h9 (pow_nonneg (by norm_num) n)
    _ = 18 ^ n := by rw [← mul_pow]; norm_num

/-- The radial function `y ↦ smoothTransition (‖y‖ - 1)` is smooth: it vanishes on the unit ball,
which hides the non-differentiability of the norm at the origin. -/
lemma smoothTransition_radial_contDiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (fun y : E => Real.smoothTransition (‖y‖ - 1)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) zero_lt_one] with y hy
    simp only [Metric.mem_ball, dist_zero_right] at hy
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · have h1 : ContDiffAt ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - 1)) (‖x‖) :=
      Real.smoothTransition.contDiffAt.comp _ (contDiffAt_id.sub contDiffAt_const)
    exact h1.comp x (contDiffAt_norm (E := E) ℝ hx)

/-- `u ↦ smoothTransition (√u - 1)` is smooth on `(0, ∞)`. -/
lemma smoothTransition_sqrt_contDiffOn :
    ContDiffOn ℝ ∞ (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun u : ℝ => Real.smoothTransition (u - 1)) Set.univ :=
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun u : ℝ => Real.sqrt u) (Set.Ioi 0) := by
    intro u hu
    exact (Real.contDiffAt_sqrt (by simpa using ne_of_gt hu)).contDiffWithinAt
  exact h1.comp h2 (fun u _ => mem_univ _)

/-- Uniform bound for the iterated derivatives of `u ↦ smoothTransition (√u - 1)` on the interval
`[1/4, 9]` (which contains `‖y‖ ^ 2` whenever `1/2 ≤ ‖y‖ ≤ 3`).  The function is smooth on
`(0, ∞)` and constant `= 1` for `u ≥ 4`, so continuity on the compact `[1/4, 9]` gives the bound. -/
lemma smoothTransition_sqrt_deriv_bound (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, i ≤ a → ∀ u : ℝ, u ∈ Set.Icc (1/4) 9 →
      ‖iteratedFDeriv ℝ i (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) u‖ ≤ C := by
  classical
  have hg := smoothTransition_sqrt_contDiffOn
  have hcont : ∀ i : ℕ, ContinuousOn
      (fun u : ℝ => iteratedFDeriv ℝ i
        (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) u) (Set.Icc (1/4) 9) := by
    intro i
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ i
        (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) (Set.Ioi 0)) (Set.Ioi 0) :=
      hg.continuousOn_iteratedFDerivWithin (m := i)
        (show ((i : ℕ∞) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top) isOpen_Ioi.uniqueDiffOn
    have h2 : ContinuousOn (fun u : ℝ => iteratedFDeriv ℝ i
        (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) u) (Set.Ioi 0) :=
      h1.congr (fun u hu => (iteratedFDerivWithin_of_isOpen i isOpen_Ioi hu).symm)
    refine h2.mono ?_
    intro u hu
    exact lt_of_lt_of_le (by norm_num) hu.1
  choose B hB using fun i => isCompact_Icc.exists_bound_of_continuousOn (hcont i)
  refine ⟨max 1 (∑ i ∈ Finset.range (a + 1), |B i|), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro i hi u hu
  refine (hB i u hu).trans ?_
  have h1 : B i ≤ |B i| := le_abs_self _
  have h2 : |B i| ≤ ∑ j ∈ Finset.range (a + 1), |B j| := by
    have hnn : ∀ j ∈ Finset.range (a+1), (0:ℝ) ≤ |B j| := fun j _ => abs_nonneg (B j)
    exact Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact (h1.trans h2).trans (le_max_right _ _)

/-- **Derivative bounds for the radial transition function `y ↦ smoothTransition (‖y‖ - 1)`,
uniformly in the ambient inner product space.**  For every `a` there is `M > 0` with
`‖D^a (y ↦ smoothTransition (‖y‖ - 1)) x‖ ≤ M` for every inner product space `E` and every `x`. -/
lemma smoothTransition_radial_norm_iteratedFDeriv_bound (a : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E),
      ‖iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (‖y‖ - 1)) x‖ ≤ M := by
  classical
  obtain ⟨C, hCpos, hC⟩ := smoothTransition_sqrt_deriv_bound a
  let M : ℝ := max ((a.factorial : ℝ) * C * 18 ^ a) 1
  have hMpos : 0 < M := lt_max_of_lt_right zero_lt_one
  refine ⟨M, hMpos, ?_⟩
  intro E _ _ x
  have hmid : 1/2 < ‖x‖ → ‖x‖ < 3 →
      ‖iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (‖y‖ - 1)) x‖
        ≤ (a.factorial : ℝ) * C * 18 ^ a := by
    intro hx1 hx3
    set s : Set E := {y : E | 1/2 < ‖y‖ ∧ ‖y‖ < 3} with hsdef
    have hsopen : IsOpen s :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hs : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
    have ht : UniqueDiffOn ℝ (Set.Ioi (1/4 : ℝ)) := isOpen_Ioi.uniqueDiffOn
    have hq : ContDiffOn ℝ ∞ (fun y : E => ‖y‖ ^ 2) s :=
      (contDiff_norm_sq ℝ (n := ∞)).contDiffOn
    have hgsm : ContDiffOn ℝ ∞ (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1))
        (Set.Ioi (1/4 : ℝ)) :=
      smoothTransition_sqrt_contDiffOn.mono (fun u hu => by
        simp only [mem_Ioi] at hu ⊢; linarith)
    have hms : MapsTo (fun y : E => ‖y‖ ^ 2) s (Set.Ioi (1/4 : ℝ)) := by
      intro y hy
      simp only [hsdef, mem_ofPred_eq, mem_Ioi] at hy ⊢
      nlinarith [hy.1, norm_nonneg y]
    have hxmem : x ∈ s := by
      simp only [hsdef, mem_ofPred_eq]; exact ⟨hx1, hx3⟩
    have hCb : ∀ i, i ≤ a → ‖iteratedFDerivWithin ℝ i
        (fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) (Set.Ioi (1/4 : ℝ))
        ((fun y : E => ‖y‖ ^ 2) x)‖ ≤ C := by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (by
        simp only [mem_Ioi]; nlinarith [hx1, norm_nonneg x])]
      refine hC i hi (‖x‖ ^ 2) ?_
      simp only [mem_Icc]
      constructor
      · nlinarith [hx1, norm_nonneg x]
      · nlinarith [hx3, norm_nonneg x]
    have hDb : ∀ i, 1 ≤ i → i ≤ a → ‖iteratedFDerivWithin ℝ i (fun y : E => ‖y‖ ^ 2) s x‖
        ≤ 18 ^ i := by
      intro i hi1 _
      rw [iteratedFDerivWithin_of_isOpen i hsopen hxmem]
      exact smoothTransition_radial_norm_sq_iteratedFDeriv_le i hi1 x hx3
    have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
      (g := fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1))
      (f := fun y : E => ‖y‖ ^ 2) (n := a) (s := s) (t := Set.Ioi (1/4 : ℝ)) (x := x)
      (N := ∞) hgsm hq (show ((a : ℕ∞) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
      ht hs hms hxmem (C := C) (D := 18) hCb hDb
    have hfun : ((fun u : ℝ => Real.smoothTransition (Real.sqrt u - 1)) ∘
        (fun y : E => ‖y‖ ^ 2)) = fun y : E => Real.smoothTransition (‖y‖ - 1) := by
      funext y
      simp only [Function.comp_apply]
      rw [Real.sqrt_sq (norm_nonneg y)]
    rw [hfun] at key
    rwa [iteratedFDerivWithin_of_isOpen a hsopen hxmem] at key
  by_cases hA : ‖x‖ ≤ 1/2
  · have hz : ‖iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (‖y‖ - 1)) x‖ ≤ 1 := by
      have hev : (fun y : E => Real.smoothTransition (‖y‖ - 1)) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
        filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1/4)] with y hy
        rw [Metric.mem_ball, dist_eq_norm] at hy
        have hyn : ‖y‖ < 1 := by
          have h2 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
            calc ‖y‖ = ‖(y - x) + x‖ := by abel_nf
              _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          linarith
        exact Real.smoothTransition.zero_of_nonpos (by linarith)
      have h1 : iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (‖y‖ - 1)) x
          = iteratedFDeriv ℝ a (fun _ : E => (0:ℝ)) x :=
        (hev.iteratedFDeriv ℝ a).eq_of_nhds
      rw [h1]
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0; rw [norm_iteratedFDeriv_zero]; norm_num
      · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) hpos.ne' (0:ℝ)]; simp
    exact hz.trans (le_trans (le_max_right _ _) le_rfl)
  · rw [not_le] at hA
    rcases lt_or_ge ‖x‖ 3 with h2 | h2
    · exact (hmid hA h2).trans (le_max_left _ _)
    · have hz : ‖iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (‖y‖ - 1)) x‖ ≤ 1 := by
        have hev : (fun y : E => Real.smoothTransition (‖y‖ - 1)) =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
          filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1/2)] with y hy
          rw [Metric.mem_ball, dist_eq_norm] at hy
          have hyn : 2 ≤ ‖y‖ := by
            have h2' : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
              calc ‖x‖ = ‖(x - y) + y‖ := by abel_nf
                _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
            rw [norm_sub_rev] at h2'
            linarith
          exact Real.smoothTransition.one_of_one_le (by linarith)
        have h1 : iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (‖y‖ - 1)) x
            = iteratedFDeriv ℝ a (fun _ : E => (1:ℝ)) x :=
          (hev.iteratedFDeriv ℝ a).eq_of_nhds
        rw [h1]
        rcases Nat.eq_zero_or_pos a with h0 | hpos
        · subst h0; rw [norm_iteratedFDeriv_zero]; norm_num
        · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) hpos.ne' (1:ℝ)]; simp
      exact hz.trans (le_trans (le_max_right _ _) le_rfl)

/-- **Derivative bounds for a rescaled radial smooth-transition cutoff.**  For each `a` there is
`C > 0` such that for every dimension `d`, every `c > 0` and every `x : ℝᵈ`,

`‖D^a (y ↦ smoothTransition (c * ‖y‖ - 1)) x‖ ≤ C * c ^ a`. -/
theorem smoothTransition_radial_iteratedFDeriv_bound (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (c : ℝ), 0 < c →
      ∀ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ a
          (fun y : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (c * ‖y‖ - 1)) x‖
          ≤ C * c ^ a := by
  obtain ⟨M, hMpos, hM⟩ := smoothTransition_radial_norm_iteratedFDeriv_bound a
  refine ⟨M + 1, by linarith, ?_⟩
  intro d c hc x
  have hF : ContDiff ℝ ((a : ℕ∞) : ℕ∞ω)
      (fun y : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (‖y‖ - 1)) :=
    (smoothTransition_radial_contDiff (E := EuclideanSpace ℝ (Fin d))).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (c * ‖y‖ - 1))
      = (fun y : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (‖c • y‖ - 1)) := by
    funext y
    rw [norm_smul, Real.norm_of_nonneg hc.le]
  rw [hfun, iteratedFDeriv_comp_const_smul (𝕜 := ℝ) c hF]
  simp only
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hc.le a)]
  calc c ^ a * ‖iteratedFDeriv ℝ a
          (fun z : EuclideanSpace ℝ (Fin d) => Real.smoothTransition (‖z‖ - 1)) (c • x)‖
      ≤ c ^ a * M := mul_le_mul_of_nonneg_left (hM (EuclideanSpace ℝ (Fin d)) (c • x))
        (pow_nonneg hc.le a)
    _ ≤ (M + 1) * c ^ a := by nlinarith [pow_nonneg hc.le a, hMpos]

end Commons.Analysis.Calculus