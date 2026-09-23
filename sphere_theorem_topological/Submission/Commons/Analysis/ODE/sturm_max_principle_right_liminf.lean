import Mathlib
import Submission.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg
import Submission.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint

namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology

/-- **Maximum principle with a right Dini condition.**  Let `a > 0`, `c < d` with `a*(d-c) < π`.
Let `w` be continuous on `[c,d]`, differentiable on `(c,d)` with derivative `w'`, and let `w'` be
differentiable with derivative `F` on `(c,d)`.  If `w c = 0`, `w'' + a^2 w ≥ 0` (i.e.
`F t + a^2 * w t ≥ 0`) on `(c,d)`, and the lower right Dini derivative of `w` at `c` is `≥ 0`
(i.e. `∀ ε > 0`, eventually `w t ≥ -ε*(t-c)` as `t → c+`), then `w ≥ 0` on `[c,d]`. -/
theorem sturm_max_principle_right_liminf {a c d : ℝ} (ha : 0 < a) (hcd : c < d)
    (hdπ : a * (d - c) < Real.pi) {w w' F : ℝ → ℝ}
    (hwcont : ContinuousOn w (Set.Icc c d))
    (hwderiv : ∀ t ∈ Set.Ioo c d, HasDerivAt w (w' t) t)
    (hw'deriv : ∀ t ∈ Set.Ioo c d, HasDerivAt w' (F t) t)
    (hwc : w c = 0)
    (hlim : ∀ ε > 0, ∀ᶠ t in nhdsWithin c (Set.Ioi c), -ε * (t - c) ≤ w t)
    (hF : ∀ t ∈ Set.Ioo c d, 0 ≤ F t + a ^ 2 * w t) :
    ∀ t ∈ Set.Icc c d, 0 ≤ w t := by
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hdc_lt : d - c < Real.pi / a := by
    rw [lt_div_iff₀ ha]; nlinarith [hdπ]
  suffices H : ∀ ε > 0, ∀ t ∈ Set.Icc c d, -ε * (t - c) ≤ w t by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hc | hct
    · rw [← hc, hwc]
    · by_contra hneg
      push Not at hneg
      have htcd : 0 < t - c := by linarith
      have hepos : 0 < -w t / (2 * (t - c)) := by
        apply div_pos
        · linarith
        · positivity
      have h := H (-w t / (2 * (t - c))) hepos t ht
      have heq : -(-w t / (2 * (t - c))) * (t - c) = w t / 2 := by
        have hne : (t - c) ≠ 0 := by linarith
        field_simp
      rw [heq] at h
      linarith
  intro ε hε
  obtain ⟨i, hci, hi'⟩ := (nhdsGT_basis c).eventually_iff.mp (hlim ε hε)
  set we : ℝ → ℝ := fun t => w t + ε * (t - c) with hwedef
  have hwe_c : we c = 0 := by change w c + ε * (c - c) = 0; rw [hwc]; ring
  have hwe_near : ∀ t ∈ Set.Ioo c i, 0 ≤ we t := by
    intro t ht
    have h := hi' ht
    change 0 ≤ w t + ε * (t - c)
    linarith
  have hwecont : ContinuousOn we (Set.Icc c d) := by
    rw [hwedef]
    exact hwcont.add ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn)
  set S : Set ℝ := {t | t ∈ Set.Icc c d ∧ ∀ s ∈ Set.Ioo c t, 0 ≤ we s} with hSdef
  have hmin_mem : min i d ∈ S := by
    refine ⟨⟨le_min hci.le hcd.le, min_le_right _ _⟩, ?_⟩
    intro s hs
    exact hwe_near s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hS_nonempty : S.Nonempty := ⟨_, hmin_mem⟩
  have hS_bdd : BddAbove S := ⟨d, fun t ht => ht.1.2⟩
  set γ := sSup S with hγdef
  have hγgt : c < γ :=
    lt_of_lt_of_le (lt_min hci hcd)
      (show min i d ≤ γ from le_csSup hS_bdd hmin_mem)
  have hγc : c ≤ γ := hγgt.le
  have hγd : γ ≤ d := csSup_le hS_nonempty (fun t ht => ht.1.2)
  have hγmem : γ ∈ Set.Icc c d := ⟨hγc, hγd⟩
  have hwe_Ioo : ∀ s ∈ Set.Ioo c γ, 0 ≤ we s := by
    intro s hs
    obtain ⟨t, htS, hst⟩ := (lt_csSup_iff hS_bdd hS_nonempty).mp (by rw [← hγdef]; exact hs.2)
    exact htS.2 s ⟨hs.1, hst⟩
  -- `we γ ≥ 0`: else `we < 0` nearby, contradicting `hwe_Ioo`.
  have hweγ_nn : 0 ≤ we γ := by
    by_contra hlt
    push Not at hlt
    have hcw := (hwecont.continuousWithinAt hγmem).preimage_mem_nhdsWithin (Iio_mem_nhds hlt)
    obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhdsWithin_iff.mp hcw
    set η' := min η (γ - c) / 2 with hη'def
    have hη'pos : 0 < η' := by rw [hη'def]; exact half_pos (lt_min hηpos (by linarith))
    have hη'ltc : η' < γ - c := by
      rw [hη'def]
      have h0 : 0 < min η (γ - c) := lt_min hηpos (by linarith)
      have := min_le_right η (γ - c)
      linarith
    have hη'ltη : η' < η := by
      rw [hη'def]
      have h0 : 0 < min η (γ - c) := lt_min hηpos (by linarith)
      have := min_le_left η (γ - c)
      linarith
    have hs_mem : γ - η' ∈ Set.Icc c d :=
      ⟨by linarith, by linarith [hγd]⟩
    have hdist : dist (γ - η') γ < η := by
      rw [Real.dist_eq]
      have : γ - η' - γ = -η' := by ring
      rw [this, abs_neg, abs_of_pos hη'pos]
      exact hη'ltη
    have hlt0 : we (γ - η') < 0 := hη ⟨Metric.mem_ball.mpr hdist, hs_mem⟩
    have hpos0 : 0 ≤ we (γ - η') := hwe_Ioo (γ - η') ⟨by linarith, by linarith⟩
    linarith
  have hwe_nn : ∀ t ∈ Set.Icc c γ, 0 ≤ we t := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with hc | hc
    · rcases lt_or_eq_of_le ht.2 with h' | h'
      · exact hwe_Ioo t ⟨hc, h'⟩
      · rw [h']; exact hweγ_nn
    · rw [← hc, hwe_c]
  have hgoal : ∀ t ∈ Set.Icc c d, 0 ≤ we t := by
    by_cases hγd' : γ = d
    · intro t ht
      exact hwe_nn t ⟨ht.1, by rw [hγd']; exact ht.2⟩
    · have hγdlt : γ < d := lt_of_le_of_ne hγd hγd'
      -- `we γ ≤ 0`
      have hweγ_le : we γ ≤ 0 := by
        by_contra hgt
        push Not at hgt
        have hcw := (hwecont.continuousWithinAt hγmem).preimage_mem_nhdsWithin (Ioi_mem_nhds hgt)
        obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhdsWithin_iff.mp hcw
        set η' := min η (d - γ) / 2 with hη'def
        have hη'pos : 0 < η' := by rw [hη'def]; exact half_pos (lt_min hηpos (by linarith))
        have hη'ltd : γ + η' ≤ d := by
          rw [hη'def]
          have h0 : 0 < min η (d - γ) := lt_min hηpos (by linarith)
          have := min_le_right η (d - γ)
          linarith
        have hη'ltη : η' < η := by
          rw [hη'def]
          have h0 : 0 < min η (d - γ) := lt_min hηpos (by linarith)
          have := min_le_left η (d - γ)
          linarith
        have hmem : γ + η' ∈ S := by
          refine ⟨⟨by linarith [hγgt], hη'ltd⟩, ?_⟩
          intro s hs
          by_cases hsle : s ≤ γ
          · rcases lt_or_eq_of_le hsle with hslt' | hseq
            · exact hwe_Ioo s ⟨hs.1, hslt'⟩
            · rw [hseq]; exact hweγ_nn
          · have hsgt : γ < s := not_le.mp hsle
            have hdist : dist s γ < η := by
              rw [Real.dist_eq]
              have : s - γ = s - γ := rfl
              rw [abs_of_pos (by linarith)]
              have : s - γ < η' := by linarith [hs.2]
              linarith
            have hgt0 : 0 < we s := hη ⟨Metric.mem_ball.mpr hdist, ⟨by linarith [hγgt], by linarith [hs.2, hγd]⟩⟩
            exact hgt0.le
        have := le_csSup hS_bdd hmem
        have : γ + η' ≤ γ := this
        linarith
      have hweγ0 : we γ = 0 := le_antisymm hweγ_le hweγ_nn
      have hrigid : Set.EqOn (fun s : ℝ => w (c + s) + ε * s) (fun _ => 0) (Set.Icc 0 (γ - c)) := by
        refine sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint (lam := a ^ 2) (t₁ := γ - c)
          (h := fun s : ℝ => w (c + s) + ε * s)
          (g := fun s : ℝ => w' (c + s) + ε) (G := fun s : ℝ => F (c + s))
          ha2 (by linarith)
          (by rw [Real.sqrt_sq ha.le]; exact lt_of_le_of_lt (by linarith [hγd]) hdc_lt)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · have h1 : ContinuousOn (fun s : ℝ => w (c + s)) (Set.Icc 0 (γ - c)) :=
            hwcont.comp ((continuous_const.add continuous_id).continuousOn)
              (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2, hγd]⟩)
          have h2 : ContinuousOn (fun s : ℝ => ε * s) (Set.Icc 0 (γ - c)) :=
            (continuous_const.mul continuous_id).continuousOn
          convert h1.add h2 using 1
          all_goals first | (ext s; simp [Pi.add_apply]) | rfl
        · rw [add_zero, mul_zero, add_zero]
          exact hwc
        · intro s hs
          have h1 : 0 ≤ we (c + s) :=
            hwe_nn (c + s) ⟨by linarith [hs.1], by linarith [hs.2, hγd]⟩
          have h2 : we (c + s) = w (c + s) + ε * s := by
            change w (c + s) + ε * ((c + s) - c) = w (c + s) + ε * s
            ring
          rw [← h2]
          exact h1
        · intro s hs
          have hmem : c + s ∈ Set.Ioo c d := ⟨by linarith [hs.1], by linarith [hs.2, hγd]⟩
          have hA : HasDerivAt (fun u : ℝ => w u) (w' (c + s)) (c + s) := hwderiv (c + s) hmem
          have hB : HasDerivAt (fun s : ℝ => c + s) (1:ℝ) s := (hasDerivAt_id s).const_add c
          have hcomp : HasDerivAt (fun s : ℝ => w (c + s)) (w' (c + s)) s := by
            convert hA.comp s hB using 1 <;> first | rfl | ring
          have hC : HasDerivAt (fun s : ℝ => ε * s) ε s := by
            simpa using (hasDerivAt_id s).const_mul ε
          exact hcomp.add hC
        · intro s hs
          have hmem : c + s ∈ Set.Ioo c d := ⟨by linarith [hs.1], by linarith [hs.2, hγd]⟩
          have hA : HasDerivAt (fun u : ℝ => w' u) (F (c + s)) (c + s) := hw'deriv (c + s) hmem
          have hB : HasDerivAt (fun s : ℝ => c + s) (1:ℝ) s := (hasDerivAt_id s).const_add c
          have hcomp : HasDerivAt (fun s : ℝ => w' (c + s)) (F (c + s)) s := by
            convert hA.comp s hB using 1 <;> first | rfl | ring
          exact hcomp.add_const ε
        · intro s hs
          have hmem : c + s ∈ Set.Ioo c d := ⟨by linarith [hs.1], by linarith [hs.2, hγd]⟩
          have h1 := hF (c + s) hmem
          have h2 : 0 ≤ a ^ 2 * (ε * s) := mul_nonneg (sq_nonneg a) (mul_nonneg hε.le hs.1.le)
          change 0 ≤ F (c + s) + a ^ 2 * (w (c + s) + ε * s)
          nlinarith [h1, h2]
        · have h3 : w (c + (γ - c)) + ε * (γ - c) = we γ := by
            change w (c + (γ - c)) + ε * (γ - c) = w γ + ε * (γ - c)
            rw [show c + (γ - c) = γ by ring]
          rw [h3, hweγ0]
      have hwe_zero : ∀ s ∈ Set.Icc c γ, we s = 0 := by
        intro s hs
        have hs' : s - c ∈ Set.Icc (0:ℝ) (γ - c) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have h1 := hrigid hs'
        have h2 : we s = w (c + (s - c)) + ε * (s - c) := by
          change w s + ε * (s - c) = w (c + (s - c)) + ε * (s - c)
          rw [show c + (s - c) = s by ring]
        rw [h2]; exact h1
      have hderiv : HasDerivAt we 0 γ := by
        have h1 : HasDerivAt we (w' γ + ε) γ := by
          have hA : HasDerivAt w (w' γ) γ := hwderiv γ ⟨hγgt, hγdlt⟩
          have hB : HasDerivAt (fun s : ℝ => ε * (s - c)) ε γ := by
            simpa using ((hasDerivAt_id γ).sub_const c).const_mul ε
          rw [hwedef]
          exact hA.add hB
        have hslope : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[<] γ] (slope we γ) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          refine ⟨Set.Ioo c γ, Ioo_mem_nhdsLT hγgt, ?_⟩
          intro x hx
          rw [slope_def_field]
          have hxmem : x ∈ Set.Icc c γ := ⟨hx.1.le, hx.2.le⟩
          rw [hwe_zero x hxmem, hweγ0, sub_self, zero_div]
        have hlim0 : Tendsto (slope we γ) (𝓝[<] γ) (𝓝 (0:ℝ)) :=
          tendsto_const_nhds.congr' hslope
        have huniq : (0:ℝ) = w' γ + ε :=
          tendsto_nhds_unique hlim0 (hasDerivAt_iff_tendsto_slope_left_right.mp h1).1
        rw [← huniq] at h1
        exact h1
      have hdπ' : a * (d - γ) < Real.pi := by
        have h1 : a * (d - γ) < a * (d - c) := mul_lt_mul_of_pos_left (by linarith [hγgt]) ha
        linarith
      have hmax : ∀ t ∈ Set.Icc γ d, 0 ≤ we t := by
        refine sturm_max_principle_right (w := we) (w' := fun t : ℝ => w' t + ε) (F := F)
          ha hγdlt hdπ' ?_ ?_ ?_ hderiv hweγ0 ?_
        · exact hwecont.mono (fun x hx => ⟨le_trans hγc hx.1, hx.2⟩)
        · intro t ht
          have hA : HasDerivAt w (w' t) t := hwderiv t ⟨lt_trans hγgt ht.1, ht.2⟩
          have hB : HasDerivAt (fun s : ℝ => ε * (s - c)) ε t := by
            simpa using ((hasDerivAt_id t).sub_const c).const_mul ε
          rw [hwedef]
          exact hA.add hB
        · intro t ht
          have hA : HasDerivAt w' (F t) t := hw'deriv t ⟨lt_trans hγgt ht.1, ht.2⟩
          simpa only using hA.add_const ε
        · intro t ht
          have h1 := hF t ⟨lt_trans hγgt ht.1, ht.2⟩
          have h2 : 0 ≤ a ^ 2 * (ε * (t - c)) := by
            have : 0 < t - c := by linarith [ht.1, hγgt]
            positivity
          change 0 ≤ F t + a ^ 2 * (w t + ε * (t - c))
          nlinarith [h1, h2]
      intro t ht
      by_cases hle : t ≤ γ
      · exact hwe_nn t ⟨ht.1, hle⟩
      · exact hmax t ⟨(not_le.mp hle).le, ht.2⟩
  intro t ht
  have := hgoal t ht
  change 0 ≤ w t + ε * (t - c) at this
  linarith

end Commons.Analysis.ODE
