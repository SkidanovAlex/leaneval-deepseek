/-
Copyright: subproject `Submission/Work/PARIMPL2/Lavaurs/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.phase_im_zero` — the Lavaurs phase is real

The single analytic export of the implosion endgame is the uniform lock-step transit with a
phase of the form `trans c = (x₀ − π/λ_c) + θ_c`, where `θ_c` is a **complex** Lavaurs
constant (`s_r − s_a` in the design note `NOTES_LEAD_mandelbar_implosion.md` §2.4).  Only the
*real* constant enters the geometry, so one has to know that `θ_c` has no imaginary part.

This file proves that: `θ_c` is forced to be real by the *antiholomorphic symmetry* of the
flower, with no estimate on `θ_c` itself.

* let `g_c = gtc c = (T_c)^[5]`, the antiholomorphic square root of the second return map
  `F_c = Ft c = g_c ∘ g_c`;
* on the `g`-invariant half-petal `fl.Pg` the attracting Fatou coordinate obeys
  `fl.φa (g_{c₀} y) = star (fl.φa y) + 1/2`, and the repelling coordinate obeys
  `fl.Ψ (star w + 1/2) = g_{c₀} (fl.Ψ w)`;
* fix the box point `y ∈ fl.Pg` and apply the lock-step transit `hL` twice at the **same**
  parameter `c`, the same time `n` and levels `u₁`, `u₂` forced into the same exit window:
  once at the box point `y` with `y' = y`, and once at the box point `g_{c₀} y` with
  `y' = g_c y`.  The two levels satisfy `u₂ − (star u₁ + 1/2) = θ_c − star θ_c = 2 i Im θ_c`
  exactly, while the two transported points agree because `g_c` commutes with `F_c`;
* `fl.Ψ` is injective on the far-left half-plane `{Re < −R₀}`.  On the fixed compact rectangle
  `K` cut out by the window a continuous injective map has a *uniform modulus of injectivity*
  (`injOn_modulus`), so letting the transit error `η → 0` forces `2 i Im θ_c = 0`.

Everything is conditional on `hL`: no constant is computed.  The bookkeeping (`n` chosen so that
the two levels land in the window, the auxiliary compact `K`, the uniform closeness
`gtc_uniform_close`) is polynomial arithmetic plus Heine–Cantor.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.injOn_modulus
import Submission.Work.PARIMPL2.Lavaurs.gtc_uniform_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedTactic false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

/-- The arithmetic identity behind the symmetric application of the lock-step transit: the two
levels differ by `θc − star θc`. -/
private lemma phase_shift (θc φy : ℂ) (t : ℝ) (n : ℕ) :
    (θc - ((t:ℝ):ℂ) + (n:ℂ) + (star φy + 1/2)) - (star (θc - ((t:ℝ):ℂ) + (n:ℂ) + φy) + 1/2)
      = θc - star θc := by
  have h : star (θc - ((t:ℝ):ℂ) + (n:ℂ) + φy) = star θc - ((t:ℝ):ℂ) + (n:ℂ) + star φy := by
    simp only [star_add, star_sub]
    simp
  rw [h]; ring

/-- The `c`-sections of the uncurried antiholomorphic square root are continuous. -/
private lemma continuous_gtc_section (y : ℂ) :
    Continuous (fun c : ℂ => Work.PARIMPL.gtc c y) := by
  have h1 : (fun c : ℂ => Work.PARIMPL.gtc c y)
      = (fun q : ℂ × ℂ => Work.PARIMPL.gtc q.1 q.2) ∘ (fun c : ℂ => (c, y)) := rfl
  rw [h1]
  exact Work.PARIMPL.continuous_uncurry_gtc.comp (continuous_id.prodMk continuous_const)

/-- Real part of `star z + 1/2`. -/
private lemma star_add_half_re (z : ℂ) : (star z + (1/2 : ℂ)).re = z.re + 1/2 := by simp

/-- Imaginary part of `star z + 1/2`. -/
private lemma star_add_half_im (z : ℂ) : (star z + (1/2 : ℂ)).im = -z.im := by simp

theorem phase_im_zero {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    {x₀ : ℝ} {θc : ℂ} {nIn : ℕ} {v : ℝ}
    (hL : Work.PARIMPL2.LockstepAll c₀ P.Nm (fun c => (((x₀ - Real.pi / P.lam c : ℝ)) : ℂ) + θc)
      nIn (fun c z => Work.PARIMPL.Ft c z) fl.Pa fl.φa fl.Ψ v)
    (hv : v = x₀ - nIn) : θc.im = 0 := by
  classical
  by_contra hU
  have hUpos : 0 < |θc.im| := abs_pos.mpr hU
  obtain ⟨y, hyPg⟩ := fl.Pg_nonempty
  have hyPa : y ∈ fl.Pa := fl.Pg_sub hyPg
  obtain ⟨R₀, hR₀inj⟩ := fl.Ψ_inj
  set Xo : ℝ := |R₀| + 10 with hXo
  set M : ℝ := -|R₀| - 2 with hM
  set H : ℝ := |(fl.φa y).im| + 1 with hH
  set Kc : ℝ := |θc.im| + H with hKc
  set K : Set ℂ := {w : ℂ | w.re ∈ Set.Icc (-Xo) M ∧ w.im ∈ Set.Icc (-Kc) Kc} with hKdef
  have hXM : Xo + M = 8 := by rw [hXo, hM]; ring
  have hMlt : M < -1 := by rw [hM]; have h := abs_nonneg R₀; linarith
  have hMnR : M < -R₀ := by rw [hM]; have h := le_abs_self R₀; linarith
  have hpy : |(fl.φa y).im| ≤ H := by rw [hH]; linarith
  have hKcomp : IsCompact K := by
    rw [hKdef]
    have hclosed : IsClosed {w : ℂ | w.re ∈ Set.Icc (-Xo) M ∧ w.im ∈ Set.Icc (-Kc) Kc} :=
      (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)
    refine (isCompact_closedBall (0:ℂ) (max |Xo| |M| + Kc + 1)).of_isClosed_subset hclosed ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have h4 := Complex.norm_le_abs_re_add_abs_im w
    have h5 : |w.re| ≤ max |Xo| |M| := by
      rw [abs_le]
      exact ⟨by linarith [hw.1.1, le_max_left |Xo| |M|, le_abs_self Xo],
             by linarith [hw.1.2, le_max_right |Xo| |M|, le_abs_self M]⟩
    have h6 : |w.im| ≤ Kc := by rw [abs_le]; exact ⟨hw.2.1, hw.2.2⟩
    linarith [h4, h5, h6]
  have hKinj : Set.InjOn fl.Ψ K := hR₀inj.mono (fun w hw => by
    show w.re < -R₀
    have h1 : w.re ≤ M := hw.1.2
    linarith [h1, hMnR])
  have hΨcont : ContinuousOn fl.Ψ K := fl.Ψ_diff.continuous.continuousOn
  let trans : ℂ → ℂ := fun c => ((x₀ - Real.pi / P.lam c : ℝ) : ℂ) + θc
  have hL' : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn (fun c z => Work.PARIMPL.Ft c z)
      fl.Pa fl.φa fl.Ψ v := hL
  have hkey : ∀ η : ℝ, 0 < η → ∃ a ∈ K, ∃ b ∈ K,
      a - b = ((2 * θc.im : ℝ) : ℂ) * Complex.I ∧ ‖fl.Ψ a - fl.Ψ b‖ ≤ 2 * η := by
    intro η hη
    set X₁ : ℝ := (fl.φa y).re with hX₁
    set K' : Set ℂ := fl.Ψ '' K with hK'def
    have hK'comp : IsCompact K' := hKcomp.image fl.Ψ_diff.continuous
    obtain ⟨ru, hrupos, hru⟩ := gtc_uniform_close (c₀ := c₀) hK'comp hη
    set η₁ : ℝ := min η (min (ru/2) (1/2)) with hη₁def
    have hη₁pos : 0 < η₁ := by
      rw [hη₁def]; exact lt_min hη (lt_min (by linarith) (by norm_num))
    have hη₁le : η₁ ≤ η := by rw [hη₁def]; exact min_le_left _ _
    have hη₁lt : η₁ < ru := by
      rw [hη₁def]
      exact lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    obtain ⟨ρ, hρ, hprop⟩ := hL' H 1 Xo η₁ X₁ hη₁pos
    set B : ℝ := Real.pi / (Xo + |θc.re| + |(fl.φa y).re| + 1) with hBdef
    have hBpos : 0 < B := by rw [hBdef]; positivity
    have hc₀ : c₀ ∈ Metric.ball c₀ P.ρ₀ := by simpa using P.hρ₀
    have hlam_ev : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c < B :=
      (P.tendsto_lam c₀ P.a2₀ hc₀).eventually (isOpen_Iio.mem_nhds hBpos)
    have hcont1 : Continuous (fun c : ℂ => Work.PARIMPL.gtc c y) := continuous_gtc_section y
    have hclos1 : ∀ᶠ c in 𝓝 c₀, ‖Work.PARIMPL.gtc c y - Work.PARIMPL.gtc c₀ y‖ < ρ := by
      have h3 : Tendsto (fun c : ℂ => Work.PARIMPL.gtc c y - Work.PARIMPL.gtc c₀ y) (𝓝 c₀) (𝓝 0) := by
        have hca : ContinuousAt (fun c : ℂ => Work.PARIMPL.gtc c y) c₀ := hcont1.continuousAt
        have hh : ContinuousAt (fun c : ℂ => Work.PARIMPL.gtc c y - Work.PARIMPL.gtc c₀ y) c₀ :=
          hca.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => Work.PARIMPL.gtc c₀ y) c₀)
        rw [ContinuousAt] at hh
        simpa using hh
      have h4 : Tendsto (fun c : ℂ => ‖Work.PARIMPL.gtc c y - Work.PARIMPL.gtc c₀ y‖) (𝓝 c₀) (𝓝 0) := by
        simpa using h3.norm
      exact h4.eventually (isOpen_Iio.mem_nhds hρ)
    have hminpos : 0 < min ρ (min ru 1) := lt_min hρ (lt_min hrupos one_pos)
    have hmem : ∀ᶠ c in 𝓝[P.Nm] c₀,
        c ∈ P.Nm ∧ P.lam c < B ∧ c ∈ Metric.ball c₀ (min ρ (min ru 1)) ∧
          ‖Work.PARIMPL.gtc c y - Work.PARIMPL.gtc c₀ y‖ < ρ := by
      filter_upwards [self_mem_nhdsWithin, hlam_ev,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds c₀ hminpos), nhdsWithin_le_nhds hclos1]
        with c hc1 hc2 hc3 hc4
      exact ⟨hc1, hc2, hc3, hc4⟩
    have hne : (𝓝[P.Nm] c₀).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (Work.PARIMPL.Nm_mem_closure d P)
    haveI := hne
    obtain ⟨c, hcNm, hclamb, hcball, hcgy⟩ := Filter.nonempty_of_mem hmem
    have hcρ : c ∈ Metric.ball c₀ ρ := by
      have h := Metric.mem_ball.mp hcball
      rw [Metric.mem_ball]; exact lt_of_lt_of_le h (min_le_left _ _)
    have hcru : ‖c - c₀‖ < ru := by
      have h := Metric.mem_ball.mp hcball
      rw [dist_eq_norm] at h
      exact lt_of_lt_of_le h ((min_le_right _ _).trans (min_le_left _ _))
    have hcmem : c ∈ P.Nm ∩ Metric.ball c₀ ρ := ⟨hcNm, hcρ⟩
    have hlampos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
    set t : ℝ := Real.pi / P.lam c with htdef
    have htbig : Xo + |θc.re| + |(fl.φa y).re| + 1 < t := by
      rw [htdef]
      have h1 : Real.pi / B < Real.pi / P.lam c :=
        div_lt_div_of_pos_left Real.pi_pos hlampos hclamb
      have h2 : Real.pi / B = Xo + |θc.re| + |(fl.φa y).re| + 1 := by
        rw [hBdef]; field_simp
      linarith
    set n : ℕ := Nat.ceil (t - θc.re - (fl.φa y).re - Xo) with hndef
    have hnlow : -Xo ≤ θc.re - t + (n : ℝ) + (fl.φa y).re := by
      have ha : t - θc.re - (fl.φa y).re - Xo ≤ (n : ℝ) := by
        rw [hndef]; exact Nat.le_ceil _
      linarith
    have hnhigh : θc.re - t + (n : ℝ) + (fl.φa y).re < M - 1/2 := by
      have h0 : 0 ≤ t - θc.re - (fl.φa y).re - Xo := by
        linarith [le_abs_self θc.re, le_abs_self (fl.φa y).re, htbig]
      have ha : (n : ℝ) < t - θc.re - (fl.φa y).re - Xo + 1 := by
        rw [hndef]; exact Nat.ceil_lt_add_one h0
      linarith [hXM]
    have hb_y1 : X₁ ≤ (fl.φa y).re := le_of_eq hX₁
    have hb_y2 : (fl.φa y).re ≤ X₁ + 1 := by rw [hX₁]; linarith
    have hb_y3 : |(fl.φa y).im| ≤ H := hpy
    have hφg : fl.φa (Work.PARIMPL.gtc c₀ y) = star (fl.φa y) + 1/2 :=
      fl.φa_fatou.1.2.2 y hyPa
    have hb_g1 : X₁ ≤ (fl.φa (Work.PARIMPL.gtc c₀ y)).re := by
      rw [hφg, hX₁, star_add_half_re]; linarith
    have hb_g2 : (fl.φa (Work.PARIMPL.gtc c₀ y)).re ≤ X₁ + 1 := by
      rw [hφg, hX₁, star_add_half_re]; linarith
    have hb_g3 : |(fl.φa (Work.PARIMPL.gtc c₀ y)).im| ≤ H := by
      rw [hφg, star_add_half_im, abs_neg]; exact hpy
    have hgPa : Work.PARIMPL.gtc c₀ y ∈ fl.Pa := fl.Pg_sub (fl.mapsTo_g_Pg hyPg)
    set u₁ : ℂ := θc - ((t : ℝ) : ℂ) + ((n : ℕ) : ℂ) + fl.φa y with hu₁
    set u₂ : ℂ := θc - ((t : ℝ) : ℂ) + ((n : ℕ) : ℂ) + fl.φa (Work.PARIMPL.gtc c₀ y) with hu₂
    set bb : ℂ := star u₁ + 1/2 with hbb
    have htrans_apply : trans c = ((x₀ - Real.pi / P.lam c : ℝ) : ℂ) + θc := rfl
    have htrans1 : trans c - (nIn : ℂ) - (v : ℂ) + ((n:ℕ):ℂ) + fl.φa y = u₁ := by
      rw [hu₁, htdef]
      simp only [htrans_apply, hv]
      push_cast
      ring
    have htrans2 : trans c - (nIn : ℂ) - (v : ℂ) + ((n:ℕ):ℂ)
        + fl.φa (Work.PARIMPL.gtc c₀ y) = u₂ := by
      rw [hu₂, htdef]
      simp only [htrans_apply, hv]
      push_cast
      ring
    have hu₁re : u₁.re = θc.re - t + (n : ℝ) + (fl.φa y).re := by
      rw [hu₁]; simp [Complex.sub_re, Complex.add_re]
    have hu₁im : u₁.im = θc.im + (fl.φa y).im := by
      rw [hu₁]; simp [Complex.sub_im, Complex.add_im]
    have hu₂re : u₂.re = θc.re - t + (n : ℝ) + (fl.φa y).re + 1/2 := by
      have h2 : u₂.re = u₁.re + 1/2 := by
        rw [hu₂, hu₁, hφg]
        simp [Complex.add_re, Complex.sub_re]
        ring
      rw [h2, hu₁re]
    have hu₂im : u₂.im = θc.im - (fl.φa y).im := by
      rw [hu₂, hφg]
      simp [Complex.add_im, Complex.sub_im, Complex.conj_im]
      ring
    have hbbre : bb.re = θc.re - t + (n : ℝ) + (fl.φa y).re + 1/2 := by
      have h1 : bb.re = u₁.re + 1/2 := by rw [hbb]; simp
      rw [h1, hu₁re]
    have hbbim : bb.im = -(θc.im + (fl.φa y).im) := by
      have h1 : bb.im = -(u₁.im) := by rw [hbb]; simp
      rw [h1, hu₁im]
    have habs1 : |θc.im + (fl.φa y).im| ≤ Kc := by
      rw [hKc]
      calc |θc.im + (fl.φa y).im| ≤ |θc.im| + |(fl.φa y).im| := abs_add_le _ _
        _ ≤ |θc.im| + H := by linarith
    have habs2 : |θc.im - (fl.φa y).im| ≤ Kc := by
      rw [hKc]
      calc |θc.im - (fl.φa y).im| = |θc.im + (-(fl.φa y).im)| := by ring_nf
        _ ≤ |θc.im| + |(-(fl.φa y).im)| := abs_add_le _ _
        _ = |θc.im| + |(fl.φa y).im| := by rw [abs_neg]
        _ ≤ |θc.im| + H := by linarith
    have hu₁K : u₁ ∈ K := by
      rw [hKdef]
      show u₁.re ∈ Set.Icc (-Xo) M ∧ u₁.im ∈ Set.Icc (-Kc) Kc
      rw [hu₁re, hu₁im]
      exact ⟨⟨by linarith [hnlow], by linarith [hnhigh]⟩,
        by linarith [(abs_le.mp habs1).1], by linarith [(abs_le.mp habs1).2]⟩
    have hu₂K : u₂ ∈ K := by
      rw [hKdef]
      show u₂.re ∈ Set.Icc (-Xo) M ∧ u₂.im ∈ Set.Icc (-Kc) Kc
      rw [hu₂re, hu₂im]
      exact ⟨⟨by linarith [hnlow], by linarith [hnhigh]⟩,
        by linarith [(abs_le.mp habs2).1], by linarith [(abs_le.mp habs2).2]⟩
    have hbbK : bb ∈ K := by
      rw [hKdef]
      show bb.re ∈ Set.Icc (-Xo) M ∧ bb.im ∈ Set.Icc (-Kc) Kc
      rw [hbbre, hbbim]
      exact ⟨⟨by linarith [hnlow], by linarith [hnhigh]⟩,
        by linarith [(abs_le.mp habs1).2], by linarith [(abs_le.mp habs1).1]⟩
    have hu1low : (-Xo) ≤ (trans c - (nIn:ℂ) - (v:ℂ) + ((n:ℕ):ℂ) + fl.φa y).re := by
      rw [htrans1, hu₁re]; exact hnlow
    have hu1up : (trans c - (nIn:ℂ) - (v:ℂ) + ((n:ℕ):ℂ) + fl.φa y).re < -1 := by
      rw [htrans1, hu₁re]; linarith [hnhigh, hMlt]
    have hu2low : (-Xo) ≤ (trans c - (nIn:ℂ) - (v:ℂ) + ((n:ℕ):ℂ)
        + fl.φa (Work.PARIMPL.gtc c₀ y)).re := by rw [htrans2, hu₂re]; linarith
    have hu2up : (trans c - (nIn:ℂ) - (v:ℂ) + ((n:ℕ):ℂ)
        + fl.φa (Work.PARIMPL.gtc c₀ y)).re < -1 := by
      rw [htrans2, hu₂re]; linarith [hnhigh, hMlt]
    have hyy : ‖y - y‖ ≤ ρ := by rw [sub_self, norm_zero]; exact le_of_lt hρ
    have happ1 : ‖(Work.PARIMPL.Ft c)^[n] y - fl.Ψ u₁‖ ≤ η₁ := by
      have h := hprop c hcmem y y n hyPa hb_y1 hb_y2 hb_y3 hyy hu1low hu1up
      simpa only [htrans1] using h
    have happ2 : ‖(Work.PARIMPL.Ft c)^[n] (Work.PARIMPL.gtc c y) - fl.Ψ u₂‖ ≤ η₁ := by
      have h := hprop c hcmem (Work.PARIMPL.gtc c₀ y) (Work.PARIMPL.gtc c y) n hgPa
        hb_g1 hb_g2 hb_g3 (le_of_lt hcgy) hu2low hu2up
      simpa only [htrans2] using h
    have hcomm : ∀ k : ℕ, (Work.PARIMPL.Ft c)^[k] (Work.PARIMPL.gtc c y)
        = Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[k] y) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
          Work.PARIMPL.Ft_eq_g_comp]
        rfl
    have hclose : ‖Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y)
        - Work.PARIMPL.gtc c₀ (fl.Ψ u₁)‖ < η :=
      hru c hcru (fl.Ψ u₁) (by rw [hK'def]; exact ⟨u₁, hu₁K, rfl⟩) ((Work.PARIMPL.Ft c)^[n] y)
        (lt_of_le_of_lt happ1 hη₁lt)
    have happ2' : ‖Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y) - fl.Ψ u₂‖ ≤ η₁ := by
      rw [← hcomm n]; exact happ2
    have hgtc_eq : fl.Ψ bb = Work.PARIMPL.gtc c₀ (fl.Ψ u₁) := by
      rw [hbb]; exact fl.Ψ_anti u₁
    have hfinal : ‖fl.Ψ u₂ - fl.Ψ bb‖ ≤ 2 * η := by
      rw [hgtc_eq]
      have e1 : ‖fl.Ψ u₂ - Work.PARIMPL.gtc c₀ (fl.Ψ u₁)‖
          ≤ ‖fl.Ψ u₂ - Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y)‖
            + ‖Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y) - Work.PARIMPL.gtc c₀ (fl.Ψ u₁)‖ := by
        have hh : (fl.Ψ u₂ - Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y))
            + (Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y) - Work.PARIMPL.gtc c₀ (fl.Ψ u₁))
            = fl.Ψ u₂ - Work.PARIMPL.gtc c₀ (fl.Ψ u₁) := by ring
        rw [← hh]
        exact norm_add_le _ _
      calc ‖fl.Ψ u₂ - Work.PARIMPL.gtc c₀ (fl.Ψ u₁)‖
          ≤ ‖fl.Ψ u₂ - Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y)‖
            + ‖Work.PARIMPL.gtc c ((Work.PARIMPL.Ft c)^[n] y) - Work.PARIMPL.gtc c₀ (fl.Ψ u₁)‖ := e1
        _ ≤ η₁ + η := add_le_add (by rw [norm_sub_rev]; exact happ2') (le_of_lt hclose)
        _ ≤ 2 * η := by linarith [hη₁le]
    have hdif : u₂ - bb = ((2 * θc.im : ℝ) : ℂ) * Complex.I := by
      have h : u₂ - bb = θc - star θc := by
        rw [hu₂, hbb, hu₁, hφg]
        exact phase_shift θc (fl.φa y) t n
      rw [h]; simpa using Complex.sub_conj θc
    exact ⟨u₂, hu₂K, bb, hbbK, hdif, hfinal⟩
  have hε : 0 < |θc.im| := abs_pos.mpr hU
  obtain ⟨δ, hδpos, hδ⟩ := injOn_modulus hKcomp hΨcont hKinj |θc.im| hε
  obtain ⟨a, haK, b, hbK, hab, hnorm⟩ := hkey (δ/4) (by linarith)
  have h1 : ‖fl.Ψ a - fl.Ψ b‖ < δ := by linarith
  have h2 : ‖a - b‖ < |θc.im| := hδ a haK b hbK h1
  have h3 : ‖a - b‖ = 2 * |θc.im| := by
    rw [hab, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  linarith

end Work.PARIMPL2.Lavaurs

end
