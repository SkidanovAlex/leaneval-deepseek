import Mathlib
import Submission.Work.Smooth.SphereJordan.flatChordSide
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic

/-!
# The winding numbers on the two sides of a straight piece differ

Let `σ : ℝ → ℂ` be a continuous `2π`-periodic plane curve which is injective on `[0, 2π)` (that is,
a simple closed curve), and suppose that near a parameter `t₀` with `σ t₀ = x` the curve runs along
the straight line through `x` in the direction of a unit vector `u`:
`σ t = x + (cc t) * u` for `|t - t₀| < δ`, with `cc t < 0` exactly for `t < t₀`.  Let `v = i u` be
`u` rotated by `90°`, so that the points `x ± ε v` lie on the two sides of the straight piece.

If the curve avoids the open segment `x + b v` (`-ε < b < ε`, `b ≠ 0`) and the two endpoints
`x ± ε v`, then the winding numbers of `σ` about the two endpoints differ: the two endpoints lie on
opposite sides of the curve.

The proof compares the two winding numbers with the index of the single loop
`c s = (σ (2π s + θ) - (x - ε v)) / (σ (2π s + θ) - (x + ε v))`, where `θ = t₀ - π` places the
crossing at the middle `s = 1/2` of the parameter interval.  The Möbius map
`w ↦ (w - (x - ε v))/(w - (x + ε v))` carries the segment between the two base points onto the
negative real axis; hence `c` meets the negative real axis exactly once, transversally, at
`s = 1/2`, and `loopIndex_ne_zero_of_crossOnce` gives `loopIndex c ≠ 0`.  Additivity of the index
(`loopIndex_mul`, `loopIndex_spec`, `loopIndex_shiftCurve`) identifies `loopIndex c` with the
difference of the two winding numbers.
-/

noncomputable section

open Set

namespace Work.Smooth.SphereJordan

/-- The inverse of a point of the slit plane again lies in the slit plane. -/
theorem inv_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) : z⁻¹ ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left
    rw [Complex.inv_re]
    exact div_pos h hns
  · right
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr h) (ne_of_gt hns)

/-- Along the straight piece through `x` in the direction of `u`, the Möbius quotient
`(w - (x - ε v)) / (w - (x + ε v))` takes the value `(r + ε i)/(r - ε i)`. -/
theorem straightBlock_quotient (x u v : ℂ) (hu : u ≠ 0) (hv : v = Complex.I * u) {ε r : ℝ}
    (hε : 0 < ε) :
    (x + (r : ℂ) * u - (x - (ε : ℂ) * v)) / (x + (r : ℂ) * u - (x + (ε : ℂ) * v))
      = (((r : ℂ) + (ε : ℂ) * Complex.I) / ((r : ℂ) - (ε : ℂ) * Complex.I)) := by
  have h1 : x + (r : ℂ) * u - (x - (ε : ℂ) * v) = ((r : ℂ) + (ε : ℂ) * Complex.I) * u := by
    rw [hv]; ring
  have h2 : x + (r : ℂ) * u - (x + (ε : ℂ) * v) = ((r : ℂ) - (ε : ℂ) * Complex.I) * u := by
    rw [hv]; ring
  rw [h1, h2, mul_div_mul_right _ _ hu]

/-- The imaginary part of `(r + ε i)/(r - ε i)`. -/
theorem straightBlock_quotient_im {ε r : ℝ} (hε : 0 < ε) :
    (((r : ℂ) + (ε : ℂ) * Complex.I) / ((r : ℂ) - (ε : ℂ) * Complex.I)).im
      = 2 * ε * r / (r ^ 2 + ε ^ 2) := by
  have hden : ((r : ℂ) - (ε : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have hrc : (r : ℂ) = (ε : ℂ) := by refine Complex.ext ?_ ?_ <;> simp_all
    have hrε : r = ε := Complex.ofReal_inj.mp hrc
    nlinarith
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero]
  rw [show Complex.normSq ((r : ℂ) - (ε : ℂ) * Complex.I) = r ^ 2 + ε ^ 2 by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring]
  field_simp
  ring

/-- Linear parametrisation of the segment from `x - ε v` to `x + ε v`. -/
theorem segment_interp (x v : ℂ) {ε s : ℝ} :
    (1 - s) * (x - (ε : ℂ) * v) + s * (x + (ε : ℂ) * v)
      = x + (((2 * s - 1) * ε : ℝ) : ℂ) * v := by
  push_cast
  ring

/-- **The two ends of a small transversal cut at a straight piece of a simple closed curve have
different winding numbers.** -/
theorem windNumber_ne_of_straight_piece {σ : ℝ → ℂ} (hσ : Continuous σ)
    (hper : Function.Periodic σ (2 * Real.pi)) (hinj : Set.InjOn σ (Set.Ico 0 (2 * Real.pi)))
    (x : ℂ) (u v : ℂ) (hu : ‖u‖ = 1) (hv : v = Complex.I * u) {cc : ℝ → ℝ}
    (hcc : Continuous cc) {t₀ δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hx : σ t₀ = x) (hpiece : ∀ t, |t - t₀| < δ → σ t = x + (cc t : ℂ) * u)
    (hmono : ∀ t, |t - t₀| < δ → (cc t < 0 ↔ t < t₀))
    (havoid : ∀ t b : ℝ, -ε < b → b < ε → b ≠ 0 → σ t ≠ x + (b : ℂ) * v)
    (hoff₁ : ∀ t : ℝ, σ t ≠ x + (ε : ℂ) * v)
    (hoff₂ : ∀ t : ℝ, σ t ≠ x - (ε : ℂ) * v) :
    windNumber σ hσ (x + (ε : ℂ) * v) ≠ windNumber σ hσ (x - (ε : ℂ) * v) := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have hv0 : v ≠ 0 := by
    rw [hv]
    exact mul_ne_zero Complex.I_ne_zero hu0
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  set zmin : ℂ := x - (ε : ℂ) * v with hzmin
  set zplus : ℂ := x + (ε : ℂ) * v with hzplus
  have hσmin : ∀ t : ℝ, σ t ≠ zmin := fun t => by rw [hzmin]; exact hoff₂ t
  have hσplus : ∀ t : ℝ, σ t ≠ zplus := fun t => by rw [hzplus]; exact hoff₁ t
  set θ : ℝ := t₀ - Real.pi with hθ
  -- #### the quotient loop
  have hcont : Continuous fun s : unitInterval =>
      (σ (2 * Real.pi * (s : ℝ) + θ) - zmin) / (σ (2 * Real.pi * (s : ℝ) + θ) - zplus) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro s
      exact sub_ne_zero.mpr (hσplus _)
  let c : C(unitInterval, ℂ) := ⟨_, hcont⟩
  have hcapp : ∀ s : unitInterval,
      c s = (σ (2 * Real.pi * (s : ℝ) + θ) - zmin) / (σ (2 * Real.pi * (s : ℝ) + θ) - zplus) :=
    fun s => rfl
  have hcne : ∀ s : unitInterval, c s ≠ 0 := by
    intro s
    rw [hcapp s]
    exact div_ne_zero (sub_ne_zero.mpr (hσmin _)) (sub_ne_zero.mpr (hσplus _))
  have hperθ : σ (2 * Real.pi + θ) = σ θ := by
    rw [add_comm]
    exact hper θ
  have hcloop : c 0 = c 1 := by
    rw [hcapp, hcapp]
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) + θ = θ := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) + θ = 2 * Real.pi + θ := by norm_num
    rw [h0, h1, hperθ]
  -- #### the crossing point
  set s₀ : unitInterval := ⟨1 / 2, by norm_num⟩ with hs₀
  have hs₀coe : (s₀ : ℝ) = 1 / 2 := rfl
  have ht₀ : (s₀ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hs₀coe]
    norm_num
  have ht₀val : 2 * Real.pi * (s₀ : ℝ) + θ = t₀ := by
    rw [hs₀coe, hθ]
    ring
  have hc₀ : c s₀ = -1 := by
    rw [hcapp, ht₀val, hx, hzmin, hzplus]
    have h1 : x - (x - (ε : ℂ) * v) = (ε : ℂ) * v := by ring
    have h2 : x - (x + (ε : ℂ) * v) = -((ε : ℂ) * v) := by ring
    rw [h1, h2, div_neg, div_self (mul_ne_zero hε0 hv0)]
  have ht₀mem : (c s₀).im = 0 := by rw [hc₀]; norm_num
  have ht₀neg : (c s₀).re < 0 := by rw [hc₀]; norm_num
  -- #### the curve meets the negative real axis only at the crossing point
  have hreal : ∀ t : unitInterval, (c t).im = 0 → (c t).re ≤ 0 → t = s₀ := by
    intro s hsim hsre
    by_contra hne
    set w : ℂ := σ (2 * Real.pi * (s : ℝ) + θ) with hw
    have hcw : c s = (w - zmin) / (w - zplus) := by rw [hcapp s, hw]
    have hseg : ∀ r : ℝ, r ∈ Set.Icc 0 1 → w ≠ (1 - r) * zmin + r * zplus := by
      intro r hr hcon
      have hb : (1 - r) * zmin + r * zplus = x + (((2 * r - 1) * ε : ℝ) : ℂ) * v := by
        rw [hzmin, hzplus, segment_interp]
      rw [hb] at hcon
      have hb1 : -ε ≤ (2 * r - 1) * ε := by nlinarith [hr.1, hr.2, hε]
      have hb2 : (2 * r - 1) * ε ≤ ε := by nlinarith [hr.1, hr.2, hε]
      rcases lt_trichotomy ((2 * r - 1) * ε) 0 with hlt | heq | hgt
      · -- `b < 0`: either `b = -ε` (the base point itself) or `-ε < b < 0 < ε`
        rcases eq_or_lt_of_le hb1 with h1 | h1
        · exact hσmin _ (by rw [← hw, hcon, ← h1, hzmin]; push_cast; ring)
        · exact havoid _ _ h1 (by linarith) (ne_of_lt hlt) (by rw [← hw]; exact hcon)
      · -- the crossing point itself: `w = x`, and injectivity modulo the period forces `s = s₀`
        have hr : r = 1 / 2 := by nlinarith [heq, hε]
        have hwx : w = x := by rw [hcon, heq]; simp
        have hval : (s : ℝ) = 1 / 2 := by
          have hσx : σ (2 * Real.pi * (s : ℝ) + θ) = σ t₀ := by rw [← hw, hwx, hx]
          obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hσx
          have hk' : (s : ℝ) - 1 / 2 = (k : ℝ) := by
            have h2 : 2 * Real.pi * ((s : ℝ) - 1 / 2) = 2 * Real.pi * (k : ℝ) := by
              rw [hθ] at hk
              linarith
            exact mul_left_cancel₀ (ne_of_gt h2π) h2
          have hk0 : k = 0 := by
            have h3 : |(k : ℝ)| < 1 := by
              rw [← hk', abs_lt]
              constructor <;> linarith [s.2.1, s.2.2]
            have h4 : ((|k| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
            exact Int.abs_lt_one_iff.mp (by exact_mod_cast h4)
          rw [hk0] at hk'
          norm_num at hk'
          linarith
        exact hne (Subtype.ext (by rw [hs₀coe]; exact hval))
      · -- `0 < b`: either `b = ε` or `0 < b < ε`
        rcases eq_or_lt_of_le hb2 with h2 | h2
        · exact hσplus _ (by rw [← hw, hcon, h2, hzplus])
        · exact havoid _ _ (by linarith) h2 (ne_of_gt hgt) (by rw [← hw]; exact hcon)
    have hslit : (w - zplus) / (w - zmin) ∈ Complex.slitPlane :=
      div_sub_mem_slitPlane_of_notMem_segment (x := zmin) (y := zplus) (z := w)
        (fun r hr => hseg r hr)
    have hcinv : c s ∈ Complex.slitPlane := by
      have h1 : c s = ((w - zplus) / (w - zmin))⁻¹ := by rw [hcw, inv_div]
      rw [h1]
      exact inv_mem_slitPlane hslit
    rw [Complex.mem_slitPlane_iff] at hcinv
    rcases hcinv with h | h
    · linarith
    · exact h hsim
  -- #### the transversal sign condition at the crossing point
  have hsign : ∃ δ' : ℝ, 0 < δ' ∧ ∀ s : unitInterval, |(s : ℝ) - (s₀ : ℝ)| < δ' →
      (s : ℝ) ≠ (s₀ : ℝ) →
      ((s : ℝ) < (s₀ : ℝ) ↔ (c s).im < 0) ∧ ((s₀ : ℝ) < (s : ℝ) ↔ 0 < (c s).im) := by
    refine ⟨min (δ / (2 * Real.pi)) (1 / 2), lt_min (div_pos hδ h2π) (by norm_num), ?_⟩
    intro s hs hsne
    rw [hs₀coe] at hs hsne ⊢
    set t : ℝ := 2 * Real.pi * (s : ℝ) + θ with htdef
    have ht' : t - t₀ = 2 * Real.pi * ((s : ℝ) - 1 / 2) := by rw [htdef, hθ]; ring
    have htabs : |t - t₀| < δ := by
      rw [ht', abs_mul, abs_of_pos h2π]
      have h6 : |(s : ℝ) - 1 / 2| < δ / (2 * Real.pi) := lt_of_lt_of_le hs (min_le_left _ _)
      calc 2 * Real.pi * |(s : ℝ) - 1 / 2| < 2 * Real.pi * (δ / (2 * Real.pi)) :=
            mul_lt_mul_of_pos_left h6 h2π
        _ = δ := by field_simp
    have htne : t ≠ t₀ := by
      intro h
      apply hsne
      have h7 : 2 * Real.pi * ((s : ℝ) - 1 / 2) = 0 := by rw [← ht', h]; ring
      rcases mul_eq_zero.mp h7 with h8 | h8
      · exact absurd h8 (ne_of_gt h2π)
      · linarith
    have ht2π : |t - t₀| < 2 * Real.pi := by
      rw [ht', abs_mul, abs_of_pos h2π]
      have h6 : |(s : ℝ) - 1 / 2| < 1 / 2 := lt_of_lt_of_le hs (min_le_right _ _)
      calc 2 * Real.pi * |(s : ℝ) - 1 / 2| < 2 * Real.pi * (1 / 2) :=
            mul_lt_mul_of_pos_left h6 h2π
        _ = Real.pi := by ring
        _ < 2 * Real.pi := by linarith [Real.pi_pos]
    have hccne : cc t ≠ 0 := by
      intro h0
      have hσr : σ t = x := by rw [hpiece t htabs, h0]; simp
      have hσx : σ t = σ t₀ := by rw [hσr, hx]
      obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hσx
      have habs : |t - t₀| = |(k : ℝ)| * (2 * Real.pi) := by
        rw [hk, abs_mul, abs_of_pos h2π]
      have hklt : |(k : ℝ)| < 1 := by
        rw [habs] at ht2π
        nlinarith [h2π]
      have hk0 : k = 0 := by
        have h4 : ((|k| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
        exact Int.abs_lt_one_iff.mp (by exact_mod_cast h4)
      refine htne ?_
      have hzero : t - t₀ = 0 := by rw [hk, hk0]; ring
      linarith
    have hmono_t : cc t < 0 ↔ t < t₀ := hmono t htabs
    have htrel : t < t₀ ↔ (s : ℝ) < 1 / 2 := by
      constructor <;> intro h <;> nlinarith [ht', h2π, h]
    have hcval : c s = ((cc t : ℂ) + (ε : ℂ) * Complex.I)
        / ((cc t : ℂ) - (ε : ℂ) * Complex.I) := by
      rw [hcapp s, hpiece t htabs, hzmin, hzplus]
      exact straightBlock_quotient x u v hu0 hv hε
    have him : (c s).im = 2 * ε * cc t / ((cc t) ^ 2 + ε ^ 2) := by
      rw [hcval]
      exact straightBlock_quotient_im (r := cc t) hε
    have hpos : 0 < (cc t) ^ 2 + ε ^ 2 := by positivity
    have hneg : (c s).im < 0 ↔ cc t < 0 := by
      rw [him, div_lt_iff₀ hpos]
      constructor <;> intro h <;> nlinarith [hε, h]
    have hposim : 0 < (c s).im ↔ 0 < cc t := by
      rw [him, div_pos_iff_of_pos_right hpos]
      constructor <;> intro h <;> nlinarith [hε, h]
    have hccpos : (1 / 2 : ℝ) < (s : ℝ) → 0 < cc t := by
      intro hgt
      have hnt : ¬ (t < t₀) := fun h => absurd (htrel.mp h) (not_lt.mpr (le_of_lt hgt))
      have hle : 0 ≤ cc t := le_of_not_gt (fun h => hnt (hmono_t.mp h))
      exact lt_of_le_of_ne hle (Ne.symm hccne)
    constructor
    · rw [hneg, hmono_t, htrel]
    · rw [hposim]
      constructor
      · exact hccpos
      · intro h
        by_contra hcon
        push_neg at hcon
        rcases lt_or_eq_of_le hcon with hlt | heq
        · exact absurd (hmono_t.mpr (htrel.mpr hlt)) (not_lt.mpr (le_of_lt h))
        · exact hsne heq
  -- #### the index of the quotient loop is non-zero
  have hne0 : loopIndex c ≠ 0 :=
    loopIndex_ne_zero_of_crossOnce hcne hcloop ht₀ ht₀mem ht₀neg hreal hsign
  -- #### comparison with the difference of the winding numbers
  let γmin : C(unitInterval, ℂ) :=
    curveLoop (fun t => σ (t + θ) - zmin)
      ((hσ.comp (continuous_id.add continuous_const)).sub continuous_const)
  let γplus : C(unitInterval, ℂ) :=
    curveLoop (fun t => σ (t + θ) - zplus)
      ((hσ.comp (continuous_id.add continuous_const)).sub continuous_const)
  have hγmin_app : ∀ s : unitInterval, γmin s = σ (2 * Real.pi * (s : ℝ) + θ) - zmin :=
    fun s => rfl
  have hγplus_app : ∀ s : unitInterval, γplus s = σ (2 * Real.pi * (s : ℝ) + θ) - zplus :=
    fun s => rfl
  have hγmin_ne : ∀ s : unitInterval, γmin s ≠ 0 := by
    intro s
    rw [hγmin_app s]
    exact sub_ne_zero.mpr (hσmin _)
  have hγplus_ne : ∀ s : unitInterval, γplus s ≠ 0 := by
    intro s
    rw [hγplus_app s]
    exact sub_ne_zero.mpr (hσplus _)
  have hγmin_loop : γmin 0 = γmin 1 := by
    rw [hγmin_app, hγmin_app]
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) + θ = θ := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) + θ = 2 * Real.pi + θ := by norm_num
    rw [h0, h1, hperθ]
  have hγplus_loop : γplus 0 = γplus 1 := by
    rw [hγplus_app, hγplus_app]
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) + θ = θ := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) + θ = 2 * Real.pi + θ := by norm_num
    rw [h0, h1, hperθ]
  obtain ⟨Λmin, hΛmin, -, -⟩ := argChangeLift γmin hγmin_ne
  obtain ⟨Λplus, hΛplus, -, -⟩ := argChangeLift γplus hγplus_ne
  have hΛd : ∀ s : unitInterval, Complex.exp ((Λmin - Λplus) s) = c s := by
    intro s
    rw [ContinuousMap.sub_apply, Complex.exp_sub, hΛmin s, hΛplus s, hcapp s, hγmin_app s,
      hγplus_app s]
  have hspec_c := loopIndex_spec c hcne hcloop (Λmin - Λplus) hΛd
  have hspec_min := loopIndex_spec γmin hγmin_ne hγmin_loop Λmin hΛmin
  have hspec_plus := loopIndex_spec γplus hγplus_ne hγplus_loop Λplus hΛplus
  have hwindmin : loopIndex γmin = windNumber σ hσ zmin :=
    loopIndex_shiftCurve hσ hper θ hσmin
  have hwindplus : loopIndex γplus = windNumber σ hσ zplus :=
    loopIndex_shiftCurve hσ hper θ hσplus
  have hkey : ((loopIndex c : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
      = ((windNumber σ hσ zmin - windNumber σ hσ zplus : ℤ) : ℂ)
        * (2 * Real.pi * Complex.I) := by
    have hdiff : (Λmin - Λplus) 1 - (Λmin - Λplus) 0
        = (Λmin 1 - Λmin 0) - (Λplus 1 - Λplus 0) := by
      simp only [ContinuousMap.sub_apply]
      ring
    rw [← hspec_c, hdiff, hspec_min, hspec_plus, hwindmin, hwindplus]
    push_cast
    ring
  have heq : loopIndex c = windNumber σ hσ zmin - windNumber σ hσ zplus := by
    have h1 : ((loopIndex c : ℤ) : ℂ)
        = ((windNumber σ hσ zmin - windNumber σ hσ zplus : ℤ) : ℂ) :=
      mul_right_cancel₀ two_pi_I_ne_zero hkey
    exact_mod_cast h1
  intro hwindeq
  exact hne0 (by rw [heq, hwindeq, sub_self])

end Work.Smooth.SphereJordan

end
