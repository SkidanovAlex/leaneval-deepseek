import Mathlib
import Submission.Work.Topology.crosscut_axis_separation_v2
import Submission.Work.Topology.no_path_of_crosscut_two_sphere_arcs
import Submission.Work.ELRig.crosscut_separation_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Separation by an arc of a disc crossing the horizontal diameter

This file proves `Work.ELRig.crossing_arc_separation`: if `A` is an injective continuous arc in the
closed disc `Metric.ball p r` with endpoints on the sphere, passing through `p` at the parameter
`s₀`, meeting the horizontal line `{im = p.im}` only at `p`, and with the imaginary parts of `A`
strictly on opposite sides of `p.im` to the left and to the right of `s₀`, then no path inside the
punctured disc `Metric.ball p r \ A '' [sL, sR]` joins `p + t` to `p - t` (`0 < t < r`).

The proof reduces to `Work.ELRig.crosscut_separation_ball` (which separates the two ends of the
*vertical* diameter by an arc crossing the vertical line `{re = p.re}`) by the similarity
`z ↦ -i (z - p) / r` of the disc onto the unit disc, which carries the horizontal diameter
`p ± t` onto the imaginary diameter of the unit disc and the imaginary part of `A` onto the real
part of the normalised arc.
-/

open Set Metric

namespace Work.ELRig

noncomputable section

/-! ## The similarity `z ↦ -i (z - p) / r` of the disc of centre `p`, radius `r` onto the unit disc -/

/-- The similarity carrying the disc `Metric.ball p r` onto the unit disc and the horizontal
diameter `p ± t` onto `∓ i t / r`. -/
private def sim (p : ℂ) (r : ℝ) (z : ℂ) : ℂ := -Complex.I * (z - p) / (r : ℂ)

private lemma sim_cont (p : ℂ) (r : ℝ) : Continuous (sim p r) := by
  unfold sim; fun_prop

private lemma sim_norm {p : ℂ} {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖sim p r z‖ = dist z p / r := by
  rw [sim, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos hr, Complex.dist_eq]

private lemma sim_injective {p : ℂ} {r : ℝ} (hr : 0 < r) : Function.Injective (sim p r) := by
  intro a b hab
  have hne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have h := congrArg (fun w => w * (r:ℂ)) hab
  simp only [sim] at h
  rw [div_mul_cancel₀ _ hne, div_mul_cancel₀ _ hne] at h
  have hI : (-Complex.I : ℂ) ≠ 0 := by simp
  have h2 : a - p = b - p := mul_left_cancel₀ hI h
  have h3 : (a - p) + p = (b - p) + p := by rw [h2]
  simpa using h3

private lemma sim_mem_ball {p : ℂ} {r : ℝ} (hr : 0 < r) (z : ℂ) :
    sim p r z ∈ Metric.ball (0:ℂ) 1 ↔ z ∈ Metric.ball p r := by
  rw [Metric.mem_ball, dist_zero_right, sim_norm hr, div_lt_one hr, Metric.mem_ball]

private lemma sim_mem_sphere {p : ℂ} {r : ℝ} (hr : 0 < r) (z : ℂ) :
    sim p r z ∈ Metric.sphere (0:ℂ) 1 ↔ z ∈ Metric.sphere p r := by
  rw [Metric.mem_sphere, dist_zero_right, sim_norm hr, div_eq_one_iff_eq (ne_of_gt hr),
    Metric.mem_sphere]

private lemma sim_re {p : ℂ} {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    (sim p r z).re = (z - p).im / r := by
  simp only [sim]
  rw [Complex.div_re]
  rw [show (-Complex.I * (z-p)).re = (z-p).im from by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]]
  rw [show (-Complex.I * (z-p)).im = -(z-p).re from by
        simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

private lemma sim_im {p : ℂ} {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    (sim p r z).im = -((z - p).re) / r := by
  simp only [sim]
  rw [Complex.div_im]
  rw [show (-Complex.I * (z-p)).re = (z-p).im from by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]]
  rw [show (-Complex.I * (z-p)).im = -(z-p).re from by
        simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

private lemma sim_p {p : ℂ} {r : ℝ} (hr : r ≠ 0) : sim p r p = 0 := by
  apply Complex.ext
  · rw [sim_re hr, Complex.zero_re]; simp
  · rw [sim_im hr, Complex.zero_im]; simp

private lemma sim_pt_real {p : ℂ} {r t : ℝ} (hr : r ≠ 0) :
    sim p r (p + (t : ℂ)) = -(((t / r : ℝ)) : ℂ) * Complex.I := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have h : p + (t:ℂ) - p = (t:ℂ) := by ring
  rw [sim, h, Complex.ofReal_div]
  field_simp

private lemma sim_mt_real {p : ℂ} {r t : ℝ} (hr : r ≠ 0) :
    sim p r (p - (t : ℂ)) = (((t / r : ℝ)) : ℂ) * Complex.I := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have h : p - (t:ℂ) - p = -(t:ℂ) := by ring
  rw [sim, h, Complex.ofReal_div]
  field_simp

/-! ## The reduction to `crosscut_separation_ball` (the "same side" crossing at `s₀`) -/

private theorem crossing_horizontal {p : ℂ} {r : ℝ} (hr : 0 < r) {A : ℝ → ℂ} {sL s₀ sR : ℝ}
    (hsL : sL < s₀) (hsR : s₀ < sR)
    (hAc : ContinuousOn A (Set.Icc sL sR)) (hAi : Set.InjOn A (Set.Icc sL sR)) (hAp : A s₀ = p)
    (hsphL : A sL ∈ Metric.sphere p r) (hsphR : A sR ∈ Metric.sphere p r)
    (hint : ∀ s ∈ Set.Ioo sL sR, A s ∈ Metric.ball p r)
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    (hL : ∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im)
    (hR : ∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im) :
    ∀ t : ℝ, 0 < t → t < r →
      ¬ JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p + (t : ℂ)) (p - (t : ℂ)) := by
  intro t ht0 htr
  have hd : 0 < sR - sL := by linarith
  have hdne : sR - sL ≠ 0 := ne_of_gt hd
  set β : ℝ → ℂ := fun u => A (sL + u * (sR - sL)) with hβdef
  set v : ℝ := (s₀ - sL) / (sR - sL) with hvdef
  have hmem : ∀ u ∈ Set.Icc (0:ℝ) 1, sL + u * (sR - sL) ∈ Set.Icc sL sR := by
    intro u hu
    constructor <;> nlinarith [hu.1, hu.2, hd]
  have hs₀mem : s₀ ∈ Set.Icc sL sR := ⟨hsL.le, hsR.le⟩
  have hcontβ : ContinuousOn β (Set.Icc (0:ℝ) 1) := by
    rw [hβdef]
    refine hAc.comp ?_ ?_
    · exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    · intro u hu; exact hmem u hu
  have hinjβ : Set.InjOn β (Set.Icc (0:ℝ) 1) := by
    intro u₁ hu₁ u₂ hu₂ h
    rw [hβdef] at h
    have h' : sL + u₁ * (sR - sL) = sL + u₂ * (sR - sL) := hAi (hmem u₁ hu₁) (hmem u₂ hu₂) h
    have h2 : u₁ * (sR - sL) = u₂ * (sR - sL) := by linarith
    exact mul_right_cancel₀ hdne h2
  have hβ0 : β 0 = A sL := by simp only [hβdef, zero_mul, add_zero]
  have hβ1 : β 1 = A sR := by
    simp only [hβdef]
    congr 1
    ring_nf
  have hβv : β v = p := by
    rw [hβdef, hvdef]
    beta_reduce
    have h2 : sL + (s₀ - sL) / (sR - sL) * (sR - sL) = s₀ := by field_simp; ring
    rw [h2, hAp]
  have hv0 : 0 < v := by rw [hvdef]; exact div_pos (by linarith) hd
  have hv1 : v < 1 := by rw [hvdef, div_lt_one hd]; linarith
  have hintβ : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 → β u ∈ Metric.ball p r := by
    intro u hu hu0 hu1
    rw [hβdef]
    refine hint _ ⟨?_, ?_⟩
    · have h1 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      nlinarith [hu.1, hu.2, hd, h1]
    · have h1 : u < 1 := lt_of_le_of_ne hu.2 hu1
      nlinarith [hu.1, hu.2, hd, h1]
  have haxβ : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (β u).im ≠ p.im := by
    intro u hu huv
    rw [hβdef]
    refine hline _ (hmem u hu) ?_
    intro hc
    apply huv
    have h2 : sL + u * (sR - sL) = s₀ := hAi (hmem u hu) hs₀mem (by rw [hc, hAp])
    rw [hvdef, eq_div_iff hdne]
    linarith
  have hsignβ : (∀ u ∈ Set.Ioo (0:ℝ) v, (β u).im < p.im) ∧
      (∀ u ∈ Set.Ioo v 1, p.im < (β u).im) := by
    constructor
    · intro u hu
      rw [hβdef]
      refine hL _ ⟨?_, ?_⟩
      · nlinarith [hu.1, hd]
      · have h2 : u * (sR - sL) < v * (sR - sL) := mul_lt_mul_of_pos_right hu.2 hd
        have hv' : v * (sR - sL) = s₀ - sL := by rw [hvdef]; field_simp
        nlinarith
    · intro u hu
      rw [hβdef]
      refine hR _ ⟨?_, ?_⟩
      · have h2 : v * (sR - sL) < u * (sR - sL) := mul_lt_mul_of_pos_right hu.1 hd
        have hv' : v * (sR - sL) = s₀ - sL := by rw [hvdef]; field_simp
        nlinarith
      · nlinarith [hu.2, hd]
  -- the normalised arc in the unit disc
  set B : ℝ → ℂ := fun u => sim p r (β u) with hBdef
  have hcontB : ContinuousOn B (Set.Icc (0:ℝ) 1) := (sim_cont p r).comp_continuousOn hcontβ
  have hinjB : Set.InjOn B (Set.Icc (0:ℝ) 1) :=
    fun a ha b hb hab => hinjβ ha hb (sim_injective hr hab)
  have hB0 : B 0 ∈ Metric.sphere (0:ℂ) 1 := (sim_mem_sphere hr (β 0)).mpr (by rw [hβ0]; exact hsphL)
  have hB1 : B 1 ∈ Metric.sphere (0:ℂ) 1 := (sim_mem_sphere hr (β 1)).mpr (by rw [hβ1]; exact hsphR)
  have hBmem : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 → B u ∈ Metric.ball (0:ℂ) 1 :=
    fun u hu hu0 hu1 => (sim_mem_ball hr (β u)).mpr (hintβ u hu hu0 hu1)
  have hBv : B v = 0 := by
    rw [hBdef]
    beta_reduce
    rw [hβv]; exact sim_p (ne_of_gt hr)
  have hBax : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (B u).re ≠ (0:ℂ).re := by
    intro u hu huv
    rw [hBdef]
    rw [sim_re (ne_of_gt hr)]
    intro hc
    have h1 : (β u - p).im = 0 := by
      rcases div_eq_zero_iff.mp hc with h | h
      · exact h
      · exact absurd h (ne_of_gt hr)
    rw [Complex.sub_im, sub_eq_zero] at h1
    exact haxβ u hu huv h1
  have hBsign : (∀ u ∈ Set.Ioo (0:ℝ) v, (B u).re < (0:ℂ).re) ∧
      (∀ u ∈ Set.Ioo v 1, (0:ℂ).re < (B u).re) := by
    constructor
    · intro u hu
      rw [hBdef]
      rw [sim_re (ne_of_gt hr), Complex.sub_im]
      exact div_neg_of_neg_of_pos (by linarith [(hsignβ.1 u hu)]) hr
    · intro u hu
      rw [hBdef]
      rw [sim_re (ne_of_gt hr), Complex.sub_im]
      exact div_pos (by linarith [(hsignβ.2 u hu)]) hr
  have hkey := crosscut_separation_ball (p := 0) (ρ := 1) (β := B) (v := v) one_pos hcontB hinjB
      hB0 hB1 hBmem hv0 hv1 hBv hBax hBsign (t / r) (div_pos ht0 hr) ((div_lt_one hr).mpr htr)
  intro hjoin
  have hjoinUnit : JoinedIn (Metric.ball (0:ℂ) 1 \ B '' Set.Icc (0:ℝ) 1)
      (sim p r (p + (t : ℂ))) (sim p r (p - (t : ℂ))) := by
    refine ⟨Path.map hjoin.somePath (sim_cont p r), ?_⟩
    intro s
    have hγs := hjoin.somePath_mem s
    simp only [Set.mem_sdiff] at hγs
    obtain ⟨hb, hna⟩ := hγs
    refine ⟨(sim_mem_ball hr _).mpr hb, ?_⟩
    rintro ⟨u, hu, hsu⟩
    have hEq : β u = hjoin.somePath s := sim_injective hr hsu
    exact hna ⟨sL + u * (sR - sL), hmem u hu, by rw [← hEq]⟩
  have h := hjoinUnit.symm
  rw [sim_mt_real (ne_of_gt hr), sim_pt_real (ne_of_gt hr)] at h
  have hkey' : ¬ JoinedIn (Metric.ball (0:ℂ) 1 \ B '' Set.Icc (0:ℝ) 1)
      ((((t / r : ℝ)) : ℂ) * Complex.I) (-((((t / r : ℝ)) : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_one, mul_one, zero_add, zero_sub] using hkey
  have h2 : JoinedIn (Metric.ball (0:ℂ) 1 \ B '' Set.Icc (0:ℝ) 1)
      ((((t / r : ℝ)) : ℂ) * Complex.I) (-((((t / r : ℝ)) : ℂ) * Complex.I)) := by
    simpa only [neg_mul] using h
  exact hkey' h2

/-! ## The main theorem -/

theorem crossing_arc_separation {p : ℂ} {r : ℝ} (hr : 0 < r) {A : ℝ → ℂ} {sL sR s₀ : ℝ}
    (hsL : sL < s₀) (hsR : s₀ < sR)
    (hAc : ContinuousOn A (Set.Icc sL sR)) (hAi : Set.InjOn A (Set.Icc sL sR)) (hAp : A s₀ = p)
    (hsphL : A sL ∈ Metric.sphere p r) (hsphR : A sR ∈ Metric.sphere p r)
    (hint : ∀ s ∈ Set.Ioo sL sR, A s ∈ Metric.ball p r)
    (hline : ∀ s ∈ Set.Icc sL sR, A s ≠ p → (A s).im ≠ p.im)
    (hcross : ((∀ s ∈ Set.Ioo sL s₀, (A s).im < p.im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, p.im < (A s).im)) ∨
        ((∀ s ∈ Set.Ioo sL s₀, p.im < (A s).im) ∧
          (∀ s ∈ Set.Ioo s₀ sR, (A s).im < p.im))) :
    ∀ t : ℝ, 0 < t → t < r →
      ¬ JoinedIn (Metric.ball p r \ (A '' Set.Icc sL sR)) (p + (t : ℂ)) (p - (t : ℂ)) := by
  rcases hcross with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · exact crossing_horizontal hr hsL hsR hAc hAi hAp hsphL hsphR hint hline hL hR
  · -- the opposite crossing: reparametrise the arc by `s ↦ sL + sR - s`
    set Ā : ℝ → ℂ := fun u => A (sL + sR - u) with hĀdef
    have h' : ∀ u ∈ Set.Icc sL sR, sL + sR - u ∈ Set.Icc sL sR := by
      intro u hu; exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
    have hĀ_cont : ContinuousOn Ā (Set.Icc sL sR) := by
      rw [hĀdef]
      refine hAc.comp ?_ ?_
      · exact (continuous_const.sub continuous_id).continuousOn
      · intro u hu; exact h' u hu
    have hĀ_inj : Set.InjOn Ā (Set.Icc sL sR) := by
      intro a ha b hb hab
      rw [hĀdef] at hab
      have h1 : sL + sR - a = sL + sR - b := hAi (h' a ha) (h' b hb) hab
      linarith
    have hĀ_p : Ā (sL + sR - s₀) = p := by
      rw [hĀdef]
      beta_reduce
      have h2 : sL + sR - (sL + sR - s₀) = s₀ := by ring
      rw [h2, hAp]
    have hĀ_sphL : Ā sL ∈ Metric.sphere p r := by
      rw [hĀdef]
      beta_reduce
      have h2 : sL + sR - sL = sR := by ring
      rw [h2]; exact hsphR
    have hĀ_sphR : Ā sR ∈ Metric.sphere p r := by
      rw [hĀdef]
      beta_reduce
      have h2 : sL + sR - sR = sL := by ring
      rw [h2]; exact hsphL
    have hĀ_hint : ∀ u ∈ Set.Ioo sL sR, Ā u ∈ Metric.ball p r := by
      intro u hu
      rw [hĀdef]
      beta_reduce
      refine hint _ ⟨?_, ?_⟩
      · linarith [hu.1, hu.2]
      · linarith [hu.1, hu.2]
    have hĀ_line : ∀ u ∈ Set.Icc sL sR, Ā u ≠ p → (Ā u).im ≠ p.im := by
      intro u hu hne
      rw [hĀdef]
      beta_reduce
      exact hline _ (h' u hu) hne
    have hĀ_L : ∀ u ∈ Set.Ioo sL (sL + sR - s₀), (Ā u).im < p.im := by
      intro u hu
      rw [hĀdef]
      beta_reduce
      refine hR _ ⟨?_, ?_⟩
      · linarith [hu.1, hu.2]
      · linarith [hu.1, hu.2]
    have hĀ_R : ∀ u ∈ Set.Ioo (sL + sR - s₀) sR, p.im < (Ā u).im := by
      intro u hu
      rw [hĀdef]
      beta_reduce
      refine hL _ ⟨?_, ?_⟩
      · linarith [hu.1, hu.2]
      · linarith [hu.1, hu.2]
    have key := crossing_horizontal (A := Ā) (s₀ := sL + sR - s₀) hr (by linarith) (by linarith)
      hĀ_cont hĀ_inj hĀ_p hĀ_sphL hĀ_sphR hĀ_hint hĀ_line hĀ_L hĀ_R
    have himg : Ā '' Set.Icc sL sR = A '' Set.Icc sL sR := by
      simp only [hĀdef]
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨sL + sR - u, h' u hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨sL + sR - u, h' u hu, ?_⟩
        change A (sL + sR - (sL + sR - u)) = A u
        congr 1; ring
    intro t ht0 htr
    rw [← himg]
    exact key t ht0 htr

end

end Work.ELRig
