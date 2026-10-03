import Mathlib

namespace Work.HornSC.JC

/-- The punctured open ball around `0` in `ℂ` of radius `r` is preconnected.

It is the continuous image of the preconnected set `(0, r) × ℝ` under the map
`(t, θ) ↦ t · exp(θ·I)`. -/
lemma isPreconnected_ball_diff_singleton {r : ℝ} :
    IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) := by
  have hcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
    fun_prop
  have hS : IsPreconnected (Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ)) :=
    isPreconnected_Ioo.prod isPreconnected_univ
  have himg : IsPreconnected ((fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
      (Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ))) := hS.image _ hcont.continuousOn
  have h_eq : (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
      (Set.Ioo (0 : ℝ) r ×ˢ (Set.univ : Set ℝ)) = Metric.ball (0 : ℂ) r \ {0} := by
    ext z
    constructor
    · rintro ⟨⟨t, θ⟩, ht, rfl⟩
      simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_Ioo] at ht ⊢
      obtain ⟨ht0, htr⟩ := ht
      have hnorm : ‖(t : ℂ) * Complex.exp (↑θ * Complex.I)‖ = t := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg ht0.le]
      constructor
      · rw [Metric.mem_ball, dist_zero_right, hnorm]; exact htr
      · rw [Set.mem_singleton_iff]
        intro h
        rw [h, norm_zero] at hnorm
        exact absurd hnorm.symm ht0.ne'
    · intro hz
      rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff] at hz
      obtain ⟨hzr, hz0⟩ := hz
      refine ⟨(‖z‖, Complex.arg z), ?_, ?_⟩
      · simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_Ioo]
        exact ⟨norm_pos_iff.mpr hz0, hzr⟩
      · simpa only [Prod.fst, Prod.snd] using Complex.norm_mul_exp_arg_mul_I z
  rwa [h_eq] at himg

/-- **A connected open subset of `ℂ` containing `0` stays connected after removing `0`.** -/
theorem isConnected_diff_singleton {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (h0 : (0 : ℂ) ∈ D) : IsConnected (D \ {0}) := by
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hDo 0 h0
  have hP : IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) := isPreconnected_ball_diff_singleton
  have hPD : Metric.ball (0 : ℂ) r \ {0} ⊆ D \ {0} := fun z hz => ⟨hrD hz.1, hz.2⟩
  -- If the punctured ball is contained in one side of a cover of `D \ {0}`, then `D` itself is
  -- separated by a suitably modified cover, contradicting the connectedness of `D`.
  have key : ∀ {U V : Set ℂ}, IsOpen U → IsOpen V → D \ {0} ⊆ U ∪ V →
      (D \ {0} ∩ U).Nonempty → (D \ {0} ∩ V).Nonempty →
      Metric.ball (0 : ℂ) r \ {0} ⊆ U → (D \ {0} ∩ (U ∩ V)).Nonempty := by
    intro U V hU hV hUV hUne hVne hPU
    by_contra hcon
    obtain ⟨a, haD, haV⟩ := hVne
    have ha0 : a ≠ 0 := by simpa using haD.2
    have haU : a ∉ U := fun haU => hcon ⟨a, haD, haU, haV⟩
    have har : r / 2 < ‖a‖ := by
      by_contra hle
      rw [not_lt] at hle
      have hza : a ∈ Metric.closedBall (0 : ℂ) (r / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hle
      exact haU (hPU ⟨Metric.closedBall_subset_ball (by linarith) hza, by simpa using ha0⟩)
    have hUo : IsOpen (U ∪ Metric.ball (0 : ℂ) r) := hU.union Metric.isOpen_ball
    have hVo : IsOpen (V ∩ (Metric.closedBall (0 : ℂ) (r / 2))ᶜ) :=
      hV.inter Metric.isClosed_closedBall.isOpen_compl
    have hsub : D ⊆ (U ∪ Metric.ball (0 : ℂ) r) ∪
        (V ∩ (Metric.closedBall (0 : ℂ) (r / 2))ᶜ) := by
      intro z hzD
      by_cases hzb : z ∈ Metric.closedBall (0 : ℂ) (r / 2)
      · by_cases hz0 : z = 0
        · subst hz0
          exact Or.inl (Or.inr (Metric.mem_ball_self hr))
        · exact Or.inl (Or.inl
            (hPU ⟨Metric.closedBall_subset_ball (by linarith) hzb, by simpa using hz0⟩))
      · have hz0 : z ≠ 0 := by
          intro h; rw [h] at hzb
          exact hzb (Metric.mem_closedBall_self (by linarith : (0 : ℝ) ≤ r / 2))
        rcases hUV ⟨hzD, by simpa using hz0⟩ with hzU | hzV
        · exact Or.inl (Or.inl hzU)
        · exact Or.inr ⟨hzV, hzb⟩
    have hUne' : (D ∩ (U ∪ Metric.ball (0 : ℂ) r)).Nonempty :=
      ⟨0, h0, Or.inr (Metric.mem_ball_self hr)⟩
    have hVne' : (D ∩ (V ∩ (Metric.closedBall (0 : ℂ) (r / 2))ᶜ)).Nonempty :=
      ⟨a, haD.1, haV, by
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]; exact not_le.mpr har⟩
    have hempty : ¬ (D ∩ ((U ∪ Metric.ball (0 : ℂ) r) ∩
        (V ∩ (Metric.closedBall (0 : ℂ) (r / 2))ᶜ))).Nonempty := by
      rintro ⟨z, hzD, hzU', hzV'⟩
      have hz0 : z ≠ 0 := by
        intro h; rw [h] at hzV'
        exact hzV'.2 (Metric.mem_closedBall_self (by linarith : (0 : ℝ) ≤ r / 2))
      rcases hzU' with hzU | hzb
      · exact hcon ⟨z, ⟨hzD, by simpa using hz0⟩, hzU, hzV'.1⟩
      · exact hcon ⟨z, ⟨hzD, by simpa using hz0⟩, hPU ⟨hzb, by simpa using hz0⟩, hzV'.1⟩
    exact absurd (hDc.2 (U ∪ Metric.ball (0 : ℂ) r)
      (V ∩ (Metric.closedBall (0 : ℂ) (r / 2))ᶜ) hUo hVo hsub hUne' hVne') hempty
  refine ⟨?_, ?_⟩
  · refine ⟨((r / 2 : ℝ) : ℂ), hrD ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · simp only [Set.mem_singleton_iff, Complex.ofReal_ne_zero]; linarith
  · intro u v hu hv huv hune hvne
    by_cases h1 : (Metric.ball (0 : ℂ) r \ {0} ∩ u).Nonempty
    · by_cases h2 : (Metric.ball (0 : ℂ) r \ {0} ∩ v).Nonempty
      · exact (hP u v hu hv (hPD.trans huv) h1 h2).mono (fun z hz => ⟨hPD hz.1, hz.2⟩)
      · have hPu : Metric.ball (0 : ℂ) r \ {0} ⊆ u := by
          intro z hz
          rcases hPD.trans huv hz with hzu | hzv
          · exact hzu
          · exact absurd ⟨z, hz, hzv⟩ h2
        exact key hu hv huv hune hvne hPu
    · have hPv : Metric.ball (0 : ℂ) r \ {0} ⊆ v := by
        intro z hz
        rcases hPD.trans huv hz with hzu | hzv
        · exact absurd ⟨z, hz, hzu⟩ h1
        · exact hzv
      have hUV' : D \ {0} ⊆ v ∪ u := fun z hz => Or.symm (huv hz)
      have hthis := key (U := v) (V := u) hv hu hUV' hvne hune hPv
      rw [Set.inter_comm v u] at hthis
      exact hthis

end Work.HornSC.JC
