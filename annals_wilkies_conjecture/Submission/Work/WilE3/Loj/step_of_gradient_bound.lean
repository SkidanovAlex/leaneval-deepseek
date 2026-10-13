/-
  One uniform steepest-descent step for a `C¹` function satisfying a Łojasiewicz-type
  gradient bound `c |g|^κ ≤ ‖∇ g‖` (`0 ≤ κ < 1`, `c > 0`) on a ball on which `g` does not vanish.

  On such a ball `g` has constant sign, so with `σ` its (constant) sign the function
  `v = σ * g` is positive and `C¹` there, `|g| = v` on the ball, and `fderiv ℝ v = σ • fderiv ℝ g`
  (so `‖fderiv ℝ v‖ = ‖fderiv ℝ g‖`).  For `z` in the inner ball the Hahn–Banach/Riesz vector
  `d` chosen by `exists_mul_apply_le_neg` (a maximiser of `fderiv ℝ v z` on the unit ball) still
  realises a fraction `1 - ε/2` of the maximal decrease of `fderiv ℝ v` at every point of the
  segment `z + [0,h₀]·d`, because `fderiv ℝ v` is *uniformly* continuous on the compact ball and
  `‖fderiv ℝ v z‖ ≥ c m^κ` where `m > 0` is the minimum of `v` there.  Hence
  `t ↦ v (z + t·d) ^ (1-κ)` has derivative `≤ -(c (1-κ) (1-ε))` on `[0,h₀)`, and the fencing
  lemma `sub_le_mul_of_hasDerivWithinAt_le` (`loj_tools.lean`) integrates this.

  The uniform step size is `h₀ = min (δ - s) ρ / 2`, where `ρ` is the uniform-continuity
  modulus of `fderiv ℝ v` on `closedBall y δ` pinned down by the error budget
  `η = ε * (c * m^κ) / 4`.
-/
import Mathlib
import Submission.Work.WilE3.Loj.loj_tools

namespace Work.WilE3.Loj

theorem step_of_gradient_bound {k : ℕ} {g : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {δ s c κ ε : ℝ}
    (hgC1 : ContDiff ℝ 1 g) (hc : 0 < c) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hs0 : 0 ≤ s) (hsδ : s < δ)
    (hnz : ∀ z ∈ Metric.closedBall y δ, g z ≠ 0)
    (hgrad : ∀ z ∈ Metric.closedBall y δ, c * |g z| ^ κ ≤ ‖fderiv ℝ g z‖) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ δ - s ∧ ∀ z ∈ Metric.closedBall y s,
      ∃ d : Fin k → ℝ, ‖d‖ ≤ 1 ∧ z + h₀ • d ∈ Metric.closedBall y δ ∧
        |g (z + h₀ • d)| ^ (1 - κ) ≤ |g z| ^ (1 - κ) - h₀ * (c * (1 - κ) * (1 - ε)) := by
  have hδpos : 0 < δ := lt_of_le_of_lt hs0 hsδ
  have hδs : 0 < δ - s := by linarith
  have hκp : 0 < 1 - κ := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  -- `g` has constant sign on the convex (= preconnected) ball, since it never vanishes there
  have hsign : (∀ z ∈ Metric.closedBall y δ, 0 < g z) ∨ (∀ z ∈ Metric.closedBall y δ, g z < 0) := by
    have hconv : Convex ℝ (Metric.closedBall y δ) := convex_closedBall y δ
    have hpre : IsPreconnected (Metric.closedBall y δ) := hconv.isPreconnected
    have himg : IsPreconnected (g '' Metric.closedBall y δ) :=
      hpre.image g (hgC1.continuous.continuousOn)
    have hord : (g '' Metric.closedBall y δ).OrdConnected := isPreconnected_iff_ordConnected.mp himg
    by_cases h : ∃ z ∈ Metric.closedBall y δ, 0 < g z
    · left
      intro z hz
      by_contra hzc
      have hgz : g z < 0 := lt_of_le_of_ne (not_lt.mp hzc) (hnz z hz)
      obtain ⟨z₁, hz₁, hz₁pos⟩ := h
      have h1 : g z ∈ g '' Metric.closedBall y δ := ⟨z, hz, rfl⟩
      have h2 : g z₁ ∈ g '' Metric.closedBall y δ := ⟨z₁, hz₁, rfl⟩
      have h3 : (0 : ℝ) ∈ Set.Icc (g z) (g z₁) := ⟨hgz.le, hz₁pos.le⟩
      obtain ⟨w, hw, hw0⟩ := hord.out h1 h2 h3
      exact hnz w hw hw0
    · right
      intro z hz
      have hle : g z ≤ 0 := by
        by_contra hc
        exact h ⟨z, hz, not_le.mp hc⟩
      exact lt_of_le_of_ne hle (hnz z hz)
  -- the constant sign `σ`, and the positive function `v = σ * g`
  obtain ⟨σ, hσmem, hσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ z ∈ Metric.closedBall y δ, 0 < σ * g z := by
    rcases hsign with hp | hn
    · exact ⟨1, Or.inl rfl, fun z hz => by simpa using hp z hz⟩
    · exact ⟨-1, Or.inr rfl, fun z hz => by simpa using hn z hz⟩
  have hσabs : |σ| = 1 := by rcases hσmem with h | h <;> simp [h]
  set v : (Fin k → ℝ) → ℝ := fun w => σ * g w with hv
  have hvC1 : ContDiff ℝ 1 v := by
    rw [hv]
    simpa [smul_eq_mul] using hgC1.const_smul σ
  have hvcont : Continuous (fderiv ℝ v) := hvC1.continuous_fderiv (by norm_num)
  have hvabs : ∀ z ∈ Metric.closedBall y δ, |g z| = v z := by
    intro z hz
    have h : 0 < σ * g z := hσ z hz
    rw [hv]
    show |g z| = σ * g z
    rw [← abs_of_pos h, abs_mul, hσabs, one_mul]
  have hfderivv : ∀ z, fderiv ℝ v z = σ • fderiv ℝ g z := by
    intro z
    have hdiff : DifferentiableAt ℝ g z := (hgC1.differentiable (by norm_num)) z
    rw [hv]
    exact fderiv_const_mul hdiff σ
  have hnormv : ∀ z, ‖fderiv ℝ v z‖ = ‖fderiv ℝ g z‖ := by
    intro z
    rw [hfderivv z, norm_smul, Real.norm_eq_abs, hσabs, one_mul]
  have hgradv : ∀ z ∈ Metric.closedBall y δ, c * (v z) ^ κ ≤ ‖fderiv ℝ v z‖ := by
    intro z hz
    calc c * (v z) ^ κ = c * |g z| ^ κ := by rw [← hvabs z hz]
      _ ≤ ‖fderiv ℝ g z‖ := hgrad z hz
      _ = ‖fderiv ℝ v z‖ := (hnormv z).symm
  have hvpos : ∀ z ∈ Metric.closedBall y δ, 0 < v z := by
    intro z hz; rw [hv]; exact hσ z hz
  -- the positive minimum `m` of `v` on the compact ball
  have hBne : (Metric.closedBall y δ).Nonempty := ⟨y, by simpa [Metric.mem_closedBall] using hδpos.le⟩
  obtain ⟨z₀, hz₀B, hz₀min⟩ := IsCompact.exists_isMinOn (s := Metric.closedBall y δ)
      (f := v) (isCompact_closedBall y δ) hBne hvC1.continuous.continuousOn
  set m : ℝ := v z₀ with hm
  have hmpos : 0 < m := by rw [hm]; exact hvpos z₀ hz₀B
  have hmle : ∀ z ∈ Metric.closedBall y δ, m ≤ v z := by
    intro z hz; rw [hm]; exact hz₀min hz
  -- the error budget `η` and the uniform-continuity modulus `ρ` of `fderiv ℝ v`
  set η : ℝ := ε * (c * m ^ κ) / 4 with hη
  have hmk : 0 < c * m ^ κ := mul_pos hc (Real.rpow_pos_of_pos hmpos κ)
  have hηpos : 0 < η := by rw [hη]; exact div_pos (mul_pos hε0 hmk) (by norm_num)
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ Metric.closedBall y δ,
      ∀ b ∈ Metric.closedBall y δ, dist a b < ρ → ‖fderiv ℝ v a - fderiv ℝ v b‖ < η := by
    have hu := (isCompact_closedBall y δ).uniformContinuousOn_of_continuous hvcont.continuousOn
    obtain ⟨ρ, hρpos, hρ⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hηpos
    exact ⟨ρ, hρpos, fun a ha b hb hab => by
      have := hρ a ha b hb hab
      simpa [dist_eq_norm] using this⟩
  -- the uniform step
  set h₀ : ℝ := min (δ - s) ρ / 2 with hh₀
  have hh₀pos : 0 < h₀ := by
    rw [hh₀]; have : 0 < min (δ - s) ρ := lt_min hδs hρpos; linarith
  have hh₀le : h₀ ≤ δ - s := by
    rw [hh₀]; have h : 0 < min (δ - s) ρ := lt_min hδs hρpos; linarith [min_le_left (δ - s) ρ]
  have hh₀lt : h₀ < ρ := by
    rw [hh₀]; have h := min_le_right (δ - s) ρ; linarith
  refine ⟨h₀, hh₀pos, hh₀le, ?_⟩
  intro z hz
  have hzB : z ∈ Metric.closedBall y δ :=
    Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp hz) hsδ.le)
  have hLzge : c * m ^ κ ≤ ‖fderiv ℝ v z‖ := by
    have h1 : m ^ κ ≤ (v z) ^ κ := Real.rpow_le_rpow hmpos.le (hmle z hzB) hκ0
    have h2 : c * m ^ κ ≤ c * (v z) ^ κ := mul_le_mul_of_nonneg_left h1 hc.le
    exact le_trans h2 (hgradv z hzB)
  have hLzpos : 0 < ‖fderiv ℝ v z‖ := lt_of_lt_of_le hmk hLzge
  have hε2 : 0 < ε / 2 := by linarith
  -- the descent direction at `z`, witnessing `1 - ε/2` of the maximal decrease
  obtain ⟨d, hd1, hd2⟩ := exists_mul_apply_le_neg (E := Fin k → ℝ) (L := fderiv ℝ v z)
      (ν := ‖fderiv ℝ v z‖) (ε := ε / 2) (σ := 1) hε2 hLzpos le_rfl (Or.inl rfl)
  have hdz : (fderiv ℝ v z) d ≤ -(1 - ε / 2) * ‖fderiv ℝ v z‖ := by simpa using hd2
  have hzδ : z + h₀ • d ∈ Metric.closedBall y δ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzy : ‖z - y‖ ≤ s := by
      have h := Metric.mem_closedBall.mp hz; rwa [dist_eq_norm] at h
    have harg : (z + h₀ • d) - y = (z - y) + h₀ • d := by abel
    have hzd : ‖h₀ • d‖ = h₀ * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg hh₀pos.le]
    calc ‖(z + h₀ • d) - y‖ = ‖(z - y) + h₀ • d‖ := by rw [harg]
      _ ≤ ‖z - y‖ + ‖h₀ • d‖ := norm_add_le _ _
      _ = ‖z - y‖ + h₀ * ‖d‖ := by rw [hzd]
      _ ≤ s + h₀ := by
            have h2 : h₀ * ‖d‖ ≤ h₀ * 1 := mul_le_mul_of_nonneg_left hd1 hh₀pos.le
            linarith
      _ ≤ δ := by linarith
  -- the whole segment stays in the outer ball
  have hγmem : ∀ t ∈ Set.Ico (0:ℝ) h₀, z + t • d ∈ Metric.closedBall y δ := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hth : t < h₀ := ht.2
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzy : ‖z - y‖ ≤ s := by
      have h := Metric.mem_closedBall.mp hz; rwa [dist_eq_norm] at h
    have harg : (z + t • d) - y = (z - y) + t • d := by abel
    have hzd : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
    calc ‖(z + t • d) - y‖ = ‖(z - y) + t • d‖ := by rw [harg]
      _ ≤ ‖z - y‖ + ‖t • d‖ := norm_add_le _ _
      _ = ‖z - y‖ + t * ‖d‖ := by rw [hzd]
      _ ≤ s + h₀ := by
            have h2 : t * ‖d‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hd1 ht0
            have h3 : t * 1 = t := by ring
            have : t * ‖d‖ ≤ h₀ := by linarith [hth.le]
            linarith
      _ ≤ δ := by linarith
  -- derivative of `t ↦ v (z + t·d) ^ (1-κ)`
  have hderiv : ∀ t ∈ Set.Ico (0:ℝ) h₀,
      HasDerivWithinAt (fun t => (v (z + t • d)) ^ (1 - κ))
        (((1 - κ) * (v (z + t • d)) ^ ((1 - κ) - 1)) * ((fderiv ℝ v (z + t • d)) d))
        (Set.Ici t) t := by
    intro t ht
    have hvpt : v (z + t • d) ≠ 0 := ne_of_gt (hvpos _ (hγmem t ht))
    have hγ : HasDerivAt (fun s : ℝ => z + s • d) d t := by
      have h1 : HasDerivAt (fun s : ℝ => s • d) d t := by
        simpa using (hasDerivAt_id (𝕜 := ℝ) t).smul_const d
      simpa using h1.const_add z
    have hgw : HasDerivAt (fun s : ℝ => v (z + s • d)) ((fderiv ℝ v (z + t • d)) d) t := by
      have hF : HasFDerivAt v (fderiv ℝ v (z + t • d)) (z + t • d) :=
        (hvC1.differentiable (by norm_num) (z + t • d)).hasFDerivAt
      exact hF.comp_hasDerivAt t hγ
    have houter : HasDerivAt (fun u : ℝ => u ^ (1 - κ))
        ((1 - κ) * (v (z + t • d)) ^ ((1 - κ) - 1)) (v (z + t • d)) :=
      Real.hasDerivAt_rpow_const (Or.inl hvpt)
    exact (houter.comp t hgw).hasDerivWithinAt
  have hcont : ContinuousOn (fun t => (v (z + t • d)) ^ (1 - κ)) (Set.Icc 0 h₀) := by
    apply Continuous.continuousOn
    have h1 : Continuous fun t : ℝ => z + t • d := by fun_prop
    have h2 : Continuous v := hvC1.continuous
    exact (h2.comp h1).rpow_const (fun t => Or.inr hκp.le)
  -- the key pointwise derivative bound on `[0, h₀)`
  have hKey : ∀ t ∈ Set.Ico (0:ℝ) h₀,
      ((1 - κ) * (v (z + t • d)) ^ ((1 - κ) - 1)) * ((fderiv ℝ v (z + t • d)) d)
        ≤ -(c * (1 - κ) * (1 - ε)) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hth : t < h₀ := ht.2
    have hmem : z + t • d ∈ Metric.closedBall y δ := hγmem t ht
    have hvw : 0 < v (z + t • d) := hvpos _ hmem
    have hdist : dist (z + t • d) z < ρ := by
      rw [dist_eq_norm]
      have harg : (z + t • d) - z = t • d := by abel
      have hzd : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
      rw [harg, hzd]
      have h2 : t * ‖d‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hd1 ht0
      have h3 : t * 1 = t := by ring
      linarith [hth.le, hh₀lt]
    have hsub : ‖fderiv ℝ v (z + t • d) - fderiv ℝ v z‖ < η := hρ _ hmem z hzB hdist
    have hX : (fderiv ℝ v (z + t • d)) d ≤ -(1 - ε / 2) * ‖fderiv ℝ v z‖ + η := by
      have hsplit : (fderiv ℝ v (z + t • d)) d
          = (fderiv ℝ v z) d + ((fderiv ℝ v (z + t • d) - fderiv ℝ v z) d) := by
        rw [sub_apply]; ring
      rw [hsplit]
      have hop : ((fderiv ℝ v (z + t • d) - fderiv ℝ v z) d)
          ≤ ‖fderiv ℝ v (z + t • d) - fderiv ℝ v z‖ * ‖d‖ :=
        le_trans (Real.le_norm_self _) (ContinuousLinearMap.le_opNorm _ _)
      have h2 : ‖fderiv ℝ v (z + t • d) - fderiv ℝ v z‖ * ‖d‖ ≤ η * 1 :=
        mul_le_mul hsub.le hd1 (norm_nonneg _) hηpos.le
      linarith
    have hbudget : (2 - ε) * η ≤ (ε / 2) * (c * m ^ κ) := by
      rw [hη]; nlinarith [hmk, hε0, hε1]
    have hbudget2 : (2 - ε) * η ≤ (ε / 2) * ‖fderiv ℝ v z‖ := by
      have hh := mul_le_mul_of_nonneg_left hLzge (by linarith : (0:ℝ) ≤ ε / 2)
      linarith
    have hLw_lt : ‖fderiv ℝ v (z + t • d)‖ < ‖fderiv ℝ v z‖ + η := by
      have hstep : ‖fderiv ℝ v (z + t • d)‖ ≤
          ‖fderiv ℝ v z‖ + ‖fderiv ℝ v (z + t • d) - fderiv ℝ v z‖ := by
        have harg : fderiv ℝ v (z + t • d)
            = fderiv ℝ v z + (fderiv ℝ v (z + t • d) - fderiv ℝ v z) := by abel
        conv_lhs => rw [harg]
        exact norm_add_le _ _
      linarith
    -- `d` still realises `1 - ε` of the maximal decrease at `z + t·d`
    have hsuff : (1 - ε) * ‖fderiv ℝ v (z + t • d)‖ ≤ (1 - ε / 2) * ‖fderiv ℝ v z‖ - η := by
      have h1 : (1 - ε) * ‖fderiv ℝ v (z + t • d)‖ < (1 - ε) * (‖fderiv ℝ v z‖ + η) :=
        mul_lt_mul_of_pos_left hLw_lt h1ε
      have h2 : (1 - ε) * (‖fderiv ℝ v z‖ + η) ≤ (1 - ε / 2) * ‖fderiv ℝ v z‖ - η := by
        nlinarith [hbudget2]
      linarith
    have hX' : (fderiv ℝ v (z + t • d)) d ≤ -(1 - ε) * ‖fderiv ℝ v (z + t • d)‖ := by linarith
    have hLwge : c ≤ (v (z + t • d)) ^ (-κ) * ‖fderiv ℝ v (z + t • d)‖ := by
      have hgv : c * (v (z + t • d)) ^ κ ≤ ‖fderiv ℝ v (z + t • d)‖ := hgradv _ hmem
      have hmult := mul_le_mul_of_nonneg_left hgv (Real.rpow_nonneg hvw.le (-κ))
      have hvr : (v (z + t • d)) ^ (-κ) * (v (z + t • d)) ^ κ = 1 := by
        rw [Real.rpow_neg hvw.le, inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hvw κ))]
      have hvc : (v (z + t • d)) ^ (-κ) * (c * (v (z + t • d)) ^ κ) = c := by
        rw [mul_comm c, ← mul_assoc, hvr, one_mul]
      rw [← hvc]
      exact hmult
    rw [show (1 - κ) - 1 = -κ by ring]
    have hposA : (0:ℝ) ≤ (1 - κ) * (v (z + t • d)) ^ (-κ) :=
      mul_nonneg hκp.le (Real.rpow_nonneg hvw.le _)
    have hstep1 := mul_le_mul_of_nonneg_left hX' hposA
    have hnegA : -((1 - κ) * (1 - ε)) ≤ 0 := by nlinarith [hκp, h1ε]
    have hstep2 : -((1 - κ) * (1 - ε)) * ((v (z + t • d)) ^ (-κ) * ‖fderiv ℝ v (z + t • d)‖)
        ≤ -((1 - κ) * (1 - ε)) * c := mul_le_mul_of_nonpos_left hLwge hnegA
    have heq2 : (1 - κ) * (v (z + t • d)) ^ (-κ) * (-(1 - ε) * ‖fderiv ℝ v (z + t • d)‖)
        = -((1 - κ) * (1 - ε)) * ((v (z + t • d)) ^ (-κ) * ‖fderiv ℝ v (z + t • d)‖) := by ring
    have htarget : -((1 - κ) * (1 - ε)) * c = -(c * (1 - κ) * (1 - ε)) := by ring
    calc (1 - κ) * (v (z + t • d)) ^ (-κ) * ((fderiv ℝ v (z + t • d)) d)
        = ((1 - κ) * (v (z + t • d)) ^ (-κ)) * ((fderiv ℝ v (z + t • d)) d) := by ring
      _ ≤ ((1 - κ) * (v (z + t • d)) ^ (-κ)) * (-(1 - ε) * ‖fderiv ℝ v (z + t • d)‖) := hstep1
      _ = -((1 - κ) * (1 - ε)) * ((v (z + t • d)) ^ (-κ) * ‖fderiv ℝ v (z + t • d)‖) := heq2
      _ ≤ -((1 - κ) * (1 - ε)) * c := hstep2
      _ = -(c * (1 - κ) * (1 - ε)) := htarget
  have hdesc := sub_le_mul_of_hasDerivWithinAt_le (φ := fun t => (v (z + t • d)) ^ (1 - κ))
      (φ' := fun t => ((1 - κ) * (v (z + t • d)) ^ ((1 - κ) - 1)) * ((fderiv ℝ v (z + t • d)) d))
      (a := 0) (b := h₀) (K := c * (1 - κ) * (1 - ε)) hh₀pos.le hcont hderiv hKey
  have hfin : |g (z + h₀ • d)| ^ (1 - κ) ≤ |g z| ^ (1 - κ) - h₀ * (c * (1 - κ) * (1 - ε)) := by
    have h1 : (v (z + h₀ • d)) ^ (1 - κ) = |g (z + h₀ • d)| ^ (1 - κ) := by
      rw [hvabs (z + h₀ • d) hzδ]
    have h2 : (v z) ^ (1 - κ) = |g z| ^ (1 - κ) := by rw [hvabs z hzB]
    have h3 := hdesc
    simp only [zero_smul, add_zero] at h3
    rw [h1, h2] at h3
    rw [sub_zero] at h3
    nlinarith [h3]
  exact ⟨d, hd1, hzδ, hfin⟩

end Work.WilE3.Loj
