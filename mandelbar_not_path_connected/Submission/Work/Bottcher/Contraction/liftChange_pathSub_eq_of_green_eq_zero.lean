import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.MRMT.Found.hasArgChange_inj
import Submission.Work.MRMT.Found.hasArgChange_sub_iff_of_norm_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction

noncomputable section

/-- The `ℝ`-extension of a path on the unit interval (clamping at the endpoints via
`Set.projIcc`).  It agrees with the path on `[0,1]`, and only its values on `[0,1]` are seen by
the notion of argument change (`Work.MRMT.QC.HasArgChange`). -/
def pathReal (δ : C(unitInterval, ℂ)) : ℝ → ℂ :=
  fun t => δ (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t)

theorem continuous_pathReal (δ : C(unitInterval, ℂ)) : Continuous (pathReal δ) :=
  δ.continuous.comp continuous_projIcc

theorem pathReal_of_mem (δ : C(unitInterval, ℂ)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    pathReal δ t = δ ⟨t, ht⟩ := by
  simp only [pathReal, Set.projIcc_of_mem _ ht]

@[simp] theorem pathReal_zero (δ : C(unitInterval, ℂ)) : pathReal δ 0 = δ 0 := by
  rw [pathReal_of_mem δ (Set.left_mem_Icc.mpr zero_le_one)]
  exact congrArg δ (Subtype.ext rfl)

@[simp] theorem pathReal_one (δ : C(unitInterval, ℂ)) : pathReal δ 1 = δ 1 := by
  rw [pathReal_of_mem δ (Set.right_mem_Icc.mpr zero_le_one)]
  exact congrArg δ (Subtype.ext rfl)

theorem pathReal_sub (γ : C(unitInterval, ℂ)) (p : ℂ) :
    pathReal (pathSub γ p) = fun t => pathReal γ t - p := by
  funext t; simp only [pathReal, pathSub_apply]

/-- `Complex.exp w = |Complex.exp w| · exp (i · Im w)`. -/
theorem exp_eq_abs_mul_exp_im (w : ℂ) :
    Complex.exp w = (Real.exp w.re : ℂ) * Complex.exp ((w.im : ℂ) * Complex.I) := by
  rw [show (Real.exp w.re : ℂ) = Complex.exp (w.re : ℂ) from Complex.ofReal_exp _ ▸ rfl]
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- **Existence of the argument change and its relation to the lift change.**

For a nowhere-zero closed path `δ` there is an integer `k` -- the argument change of `δ` -- such
that `Work.MRMT.QC.HasArgChange (pathReal δ) k` and the lift change of `δ` through the
exponential covering equals `k · 2πi`. -/
theorem exists_hasArgChange_liftChange (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (hloop : δ 1 = δ 0) :
    ∃ k : ℤ, Work.MRMT.QC.HasArgChange (pathReal δ) k ∧
      liftChange δ hδ = k * (2 * Real.pi * Complex.I) := by
  obtain ⟨n, hn⟩ := liftChange_mem_zmultiples δ hδ hloop
  refine ⟨n, ?_, hn⟩
  set L := liftOf δ hδ (Complex.log (δ 0)) (Complex.exp_log (hδ 0)) with hL
  set Θ : ℝ → ℝ := fun t => (L (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t)).im with hΘ
  refine ⟨Θ, ⟨?_, ?_⟩, ?_⟩
  · exact (Complex.continuous_im.comp (L.continuous.comp continuous_projIcc)).continuousOn
  · intro t ht
    have hproj : Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t = ⟨t, ht⟩ :=
      Set.projIcc_of_mem _ ht
    have hΘt : Θ t = (L ⟨t, ht⟩).im := by rw [hΘ]; simp only; rw [hproj]
    have hLt : Complex.exp (L ⟨t, ht⟩) = δ ⟨t, ht⟩ := exp_liftOf δ hδ _ _ ⟨t, ht⟩
    have hnorm : (Real.exp (L ⟨t, ht⟩).re : ℂ) = (‖pathReal δ t‖ : ℂ) := by
      rw [← Complex.norm_exp (L ⟨t, ht⟩), hLt, ← pathReal_of_mem δ ht]
    calc pathReal δ t = δ ⟨t, ht⟩ := pathReal_of_mem δ ht
      _ = Complex.exp (L ⟨t, ht⟩) := hLt.symm
      _ = (Real.exp (L ⟨t, ht⟩).re : ℂ) * Complex.exp (((L ⟨t, ht⟩).im : ℂ) * Complex.I) :=
            exp_eq_abs_mul_exp_im _
      _ = (‖pathReal δ t‖ : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
            rw [hnorm, ← hΘt]
  · have hproj1 : Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) 1 = (1 : unitInterval) :=
      Subtype.ext (by norm_num)
    have hproj0 : Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) 0 = (0 : unitInterval) :=
      Subtype.ext (by norm_num)
    have hΘ1 : Θ 1 = (L 1).im := by rw [hΘ]; simp only; rw [hproj1]
    have hΘ0 : Θ 0 = (L 0).im := by rw [hΘ]; simp only; rw [hproj0]
    have hLdiff : L 1 - L 0 = liftChange δ hδ := by
      rw [liftChange, hL, liftOf_apply_zero]
    have him : (liftChange δ hδ).im = 2 * Real.pi * (n : ℝ) := by
      rw [hn]
      rw [show (↑n * (2 * ↑Real.pi * Complex.I)) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      simp
    rw [hΘ1, hΘ0, ← Complex.sub_im, hLdiff, him]

/-- Two points of a preconnected subset of `{green c = 0}`, seen from a closed loop `γ` on which
`green c` is positive, induce the same lift change of the translated loop `γ - ·`; equivalently,
`γ` has the same winding number about both points. -/
theorem liftChange_pathSub_eq_of_green_eq_zero (c : ℂ)
    (hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z = 0})
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (hγ : ∀ t, 0 < Work.Bottcher.green c (γ t))
    {p q : ℂ} (hp : Work.Bottcher.green c p = 0) (hq : Work.Bottcher.green c q = 0)
    (h₁ : ∀ t, Work.Bottcher.Contraction.pathSub γ p t ≠ 0)
    (h₂ : ∀ t, Work.Bottcher.Contraction.pathSub γ q t ≠ 0) :
    Work.Bottcher.Contraction.liftChange (Work.Bottcher.Contraction.pathSub γ p) h₁ =
      Work.Bottcher.Contraction.liftChange (Work.Bottcher.Contraction.pathSub γ q) h₂ := by
  classical
  set a : ℝ → ℂ := pathReal γ with hadef
  set U : Set ℂ := {w : ℂ | ∀ t : unitInterval, γ t ≠ w} with hUdef
  have ha_eq : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1), a t = γ ⟨t, ht⟩ := by
    intro t ht; rw [hadef]; exact pathReal_of_mem γ ht
  have ha1 : a 1 = γ 1 := ha_eq 1 (Set.right_mem_Icc.mpr zero_le_one)
  have ha0 : a 0 = γ 0 := ha_eq 0 (Set.left_mem_Icc.mpr zero_le_one)
  -- `K = {green c = 0}` is disjoint from the loop, hence contained in `U`
  have hKU : ∀ z : ℂ, Work.Bottcher.green c z = 0 → z ∈ U := by
    intro z hz
    rw [hUdef]
    intro t htz
    have h1 : Work.Bottcher.green c (γ t) = 0 := by rw [htz, hz]
    linarith [hγ t]
  -- argument change and lift change of the loop through `p`
  obtain ⟨n_p, hn_p_arg, hn_p_lc⟩ :=
    exists_hasArgChange_liftChange (pathSub γ p) h₁ (by simp [pathSub, hloop])
  rw [pathReal_sub γ p] at hn_p_arg
  -- the open set of points whose argument change equals that of `p`
  set A : Set ℂ :=
    {w : ℂ | Work.MRMT.QC.HasArgChange (fun t : ℝ => a t - w) n_p} ∩ U with hAdef
  have hmemA : ∀ w : ℂ, w ∈ A ↔
      Work.MRMT.QC.HasArgChange (fun t : ℝ => a t - w) n_p ∧ w ∈ U := by
    intro w; rw [hAdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro w hw
    obtain ⟨hwarg, hwU⟩ := (hmemA w).mp hw
    have hcont : ContinuousOn (fun t : ℝ => ‖a t - w‖) (Set.Icc 0 1) :=
      ((continuous_pathReal γ).sub continuous_const).norm.continuousOn
    obtain ⟨t₀, ht₀, hmin⟩ :=
      isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hcont
    have hne₀ : a t₀ - w ≠ 0 := by
      intro h0
      have h1 : γ ⟨t₀, ht₀⟩ = w := by rw [← ha_eq t₀ ht₀]; exact sub_eq_zero.mp h0
      exact hwU ⟨t₀, ht₀⟩ h1
    have hmpos : 0 < ‖a t₀ - w‖ := norm_pos_iff.mpr hne₀
    refine ⟨‖a t₀ - w‖ / 2, half_pos hmpos, ?_⟩
    intro w' hw'
    have hdist : ‖w' - w‖ < ‖a t₀ - w‖ / 2 := by
      have h := Metric.mem_ball.mp hw'; rwa [Complex.dist_eq] at h
    have hlt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w' - w‖ < ‖a t - w‖ := by
      intro t ht
      have hb : ‖a t₀ - w‖ ≤ ‖a t - w‖ := hmin ht
      linarith [hdist, hb, norm_nonneg (a t₀ - w)]
    have hloopw : (fun t : ℝ => a t - w) 1 = (fun t : ℝ => a t - w) 0 := by
      simp only [ha1, ha0, hloop]
    have hloopw' : (fun t : ℝ => a t - w') 1 = (fun t : ℝ => a t - w') 0 := by
      simp only [ha1, ha0, hloop]
    have hcontw : ContinuousOn (fun t : ℝ => a t - w) (Set.Icc 0 1) :=
      ((continuous_pathReal γ).sub continuous_const).continuousOn
    have hcontw' : ContinuousOn (fun t : ℝ => a t - w') (Set.Icc 0 1) :=
      ((continuous_pathReal γ).sub continuous_const).continuousOn
    rw [hmemA]
    refine ⟨?_, ?_⟩
    · refine Work.MRMT.QC.hasArgChange_of_close hwarg hloopw hloopw' hcontw hcontw' ?_
      intro t ht
      have h2 : (a t - w') - (a t - w) = w - w' := by ring
      rw [h2, norm_sub_rev]
      exact hlt t ht
    · intro t ht
      have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t.2
      have h3 : a (t : ℝ) = w' := by
        rw [ha_eq (t : ℝ) htI]
        rw [show (⟨(t : ℝ), htI⟩ : unitInterval) = t from Subtype.ext rfl]
        exact ht
      have h4 := hlt (t : ℝ) htI
      rw [h3] at h4
      exact lt_irrefl _ h4
  -- `A` is closed inside `K`
  have hclos : closure A ∩ {z : ℂ | Work.Bottcher.green c z = 0} ⊆ A := by
    intro y hy
    obtain ⟨hycl, hyK⟩ := hy
    have hygreen : Work.Bottcher.green c y = 0 := by simpa using hyK
    have hyU : y ∈ U := hKU y hygreen
    obtain ⟨n_y, hn_y_arg, _⟩ :=
      exists_hasArgChange_liftChange (pathSub γ y)
        (fun t => sub_ne_zero.mpr (hyU t)) (by simp [pathSub, hloop])
    rw [pathReal_sub γ y] at hn_y_arg
    have hcont : ContinuousOn (fun t : ℝ => ‖a t - y‖) (Set.Icc 0 1) :=
      ((continuous_pathReal γ).sub continuous_const).norm.continuousOn
    obtain ⟨s₀, hs₀, hmin⟩ :=
      isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hcont
    have hne₀ : a s₀ - y ≠ 0 := by
      intro h0
      have h1 : γ ⟨s₀, hs₀⟩ = y := by rw [← ha_eq s₀ hs₀]; exact sub_eq_zero.mp h0
      exact hyU ⟨s₀, hs₀⟩ h1
    have hmpos : 0 < ‖a s₀ - y‖ := norm_pos_iff.mpr hne₀
    obtain ⟨w', hw'A, hw'y⟩ :=
      Metric.mem_closure_iff.mp hycl (‖a s₀ - y‖ / 2) (half_pos hmpos)
    have hdist : ‖w' - y‖ < ‖a s₀ - y‖ / 2 := by
      rw [Complex.dist_eq, norm_sub_rev] at hw'y; exact hw'y
    obtain ⟨hw'arg, hw'U⟩ := (hmemA w').mp hw'A
    have hnear0 : Work.MRMT.QC.HasArgChange (fun t : ℝ => a t - y) n_y :=
      Work.MRMT.QC.hasArgChange_congr hn_y_arg (fun t => by rw [hadef])
    have hnear : Work.MRMT.QC.HasArgChange (fun t : ℝ => a t - w') n_y := by
      refine Work.MRMT.QC.hasArgChange_of_close hnear0 ?_ ?_ ?_ ?_ ?_
      · simp only [ha1, ha0, hloop]
      · simp only [ha1, ha0, hloop]
      · exact ((continuous_pathReal γ).sub continuous_const).continuousOn
      · exact ((continuous_pathReal γ).sub continuous_const).continuousOn
      · intro t ht
        have h2 : (a t - w') - (a t - y) = y - w' := by ring
        rw [h2, norm_sub_rev]
        have hb : ‖a s₀ - y‖ ≤ ‖a t - y‖ := hmin ht
        linarith [hdist, hb, norm_nonneg (a s₀ - y)]
    have hw'ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => a t - w') t ≠ 0 := by
      intro t ht h0
      have h1 : a t = w' := sub_eq_zero.mp h0
      have h2 : γ ⟨t, ht⟩ = w' := by rw [← ha_eq t ht]; exact h1
      exact hw'U ⟨t, ht⟩ h2
    have hny : n_y = n_p := Work.MRMT.Found.hasArgChange_inj hw'ne hnear hw'arg
    rw [hmemA]
    exact ⟨by rw [← hny]; exact hn_y_arg, hyU⟩
  have hpU : p ∈ U := hKU p hp
  have hpA : p ∈ A := by
    rw [hmemA]
    exact ⟨hn_p_arg, hpU⟩
  have hKA : {z : ℂ | Work.Bottcher.green c z = 0} ⊆ A :=
    hK.subset_of_closure_inter_subset hAopen ⟨p, hp, hpA⟩ hclos
  have hqA : q ∈ A := hKA hq
  obtain ⟨hq_arg, hqU⟩ := (hmemA q).mp hqA
  obtain ⟨n_q, hn_q_arg, hn_q_lc⟩ :=
    exists_hasArgChange_liftChange (pathSub γ q) h₂ (by simp [pathSub, hloop])
  rw [pathReal_sub γ q] at hn_q_arg
  have hqne : ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => a t - q) t ≠ 0 := by
    intro t ht h0
    have h1 : a t = q := sub_eq_zero.mp h0
    have h2 : γ ⟨t, ht⟩ = q := by rw [← ha_eq t ht]; exact h1
    exact hqU ⟨t, ht⟩ h2
  have hnpnq : n_q = n_p := Work.MRMT.Found.hasArgChange_inj hqne hn_q_arg hq_arg
  rw [hn_p_lc, hn_q_lc, hnpnq]


end

end Work.Bottcher.Contraction
