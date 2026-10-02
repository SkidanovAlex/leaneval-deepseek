import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_eq_zero
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

/--
Generalises `Work.Bottcher.Contraction.liftChange_pathSub_eq_of_green_eq_zero` from the level set
`{green c · = 0}` to the sublevel set `{z | green c z ≤ s}`.

If `γ` is a closed path on which the Green function exceeds `s`, and `p`, `q` lie in the
preconnected set `K = {z | green c z ≤ s}` (which is therefore disjoint from the image of `γ`),
then the winding numbers of `γ` about `p` and about `q` coincide; equivalently the lift changes
through the exponential covering of `t ↦ γ t - p` and `t ↦ γ t - q` agree.

The proof is *verbatim* the proof of the existing `_of_green_eq_zero` version: copy that file and
replace the closed level set `{green c · = 0}` by `{green c · ≤ s}` and the hypothesis
`0 < green c (γ t)` by `s < green c (γ t)`.  Green is used in that proof only to show that the
special points lie in `K` and that `K` is disjoint from the loop; both uses transport unchanged
via `green c z ≤ s < green c (γ t)`.
-/
theorem liftChange_pathSub_eq_of_green_le (c : ℂ) (s : ℝ)
    (hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z ≤ s})
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (hγ : ∀ t, s < Work.Bottcher.green c (γ t))
    {p q : ℂ} (hp : Work.Bottcher.green c p ≤ s) (hq : Work.Bottcher.green c q ≤ s)
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
  -- `K = {green c ≤ s}` is disjoint from the loop, hence contained in `U`
  have hKU : ∀ z : ℂ, Work.Bottcher.green c z ≤ s → z ∈ U := by
    intro z hz
    rw [hUdef]
    intro t htz
    have h1 : Work.Bottcher.green c (γ t) ≤ s := by rw [htz]; exact hz
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
  have hclos : closure A ∩ {z : ℂ | Work.Bottcher.green c z ≤ s} ⊆ A := by
    intro y hy
    obtain ⟨hycl, hyK⟩ := hy
    have hygreen : Work.Bottcher.green c y ≤ s := by simpa using hyK
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
  have hKA : {z : ℂ | Work.Bottcher.green c z ≤ s} ⊆ A :=
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
