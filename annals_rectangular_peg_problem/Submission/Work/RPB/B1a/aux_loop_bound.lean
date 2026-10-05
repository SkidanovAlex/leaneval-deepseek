import Mathlib

/-!
# Auxiliary estimates for the straight-line loop family

Node `N2` of the conformal-map route (`RECTPEG_B1_LEAD.md`, `Submission/Work/RPB/B1a/`) asks that
every smooth embedded loop `u : ℝ → ℂ` has a `C¹`-neighbourhood consisting of loops, the
straight-line interpolant being a valid loop family.  The proof needs two kinds of quantitative
input, both collected here.

* `local_lower_bound` — near a point where the derivative does not vanish, `u` is bi-Lipschitz
  below with constant `‖u' x‖ / 2`.  This is the quantitative content of *strict*
  differentiability (`HasStrictDerivAt`), which Mathlib provides for `C¹` functions.
* `norm_sub_add_le_of_norm_deriv_le` — the mean value bound, in the form needed for the periodic
  perturbation `δ = v - u`.
* `exists_abs_le_pi_representative` and `eq_zero_of_eq_int_mul_two_pi` — the two elementary
  arithmetic facts about representatives modulo `2π` used to turn the "distance mod `2π`"
  into an ordinary `|h| ≤ π`: every real difference can be shifted by an integer multiple of `2π`
  into `[-π, π]`, and an integer multiple of `2π` that is not `0` has modulus at least `2π`.
-/

set_option autoImplicit false

open Filter Asymptotics Set Metric
open scoped Topology

noncomputable section

namespace Work.RPB.B1a

/-- **Local bi-Lipschitz lower bound.**  Let `u : ℝ → ℂ` be `C¹` with `deriv u x ≠ 0`.  Then on a
neighbourhood of `x`,
`(‖deriv u x‖ / 2) * |y - z| ≤ ‖u y - u z‖`.

(Strict differentiability at `x` gives `u y - u z = (y - z) • deriv u x + o(y - z)` uniformly for
`y, z → x`; the triangle inequality then gives the claimed bound.) -/
lemma local_lower_bound (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (x : ℝ) (hx : deriv u x ≠ 0) :
    ∃ δ > 0, ∀ y z : ℝ, |y - x| < δ → |z - x| < δ →
      (‖deriv u x‖ / 2) * |y - z| ≤ ‖u y - u z‖ := by
  have hstrict : HasStrictDerivAt u (deriv u x) x := hu.contDiffAt.hasStrictDerivAt (by norm_num)
  have hlit : (fun p : ℝ × ℝ => u p.1 - u p.2 - (p.1 - p.2) • deriv u x) =o[𝓝 (x, x)]
      (fun p : ℝ × ℝ => p.1 - p.2) := hstrict.isLittleO
  have hpos : (0 : ℝ) < ‖deriv u x‖ / 2 := by positivity
  have hev := hlit.def hpos
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  refine ⟨δ, hδpos, fun y z hy hz => ?_⟩
  have hd : max (dist y x) (dist z x) < δ := by
    rw [max_lt_iff]
    exact ⟨by simpa [Real.dist_eq] using hy, by simpa [Real.dist_eq] using hz⟩
  have hb : ‖u y - u z - (y - z) • deriv u x‖ ≤ ‖deriv u x‖ / 2 * |y - z| := by
    have := hδ (show dist (y, z) (x, x) < δ by simpa [Prod.dist_eq] using hd)
    simpa [Real.norm_eq_abs] using this
  have hs : ‖(y - z) • deriv u x‖ = |y - z| * ‖deriv u x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(y - z) • deriv u x‖ ≤ ‖u y - u z‖ + ‖u y - u z - (y - z) • deriv u x‖ := by
    have e : (y - z) • deriv u x = (u y - u z) - (u y - u z - (y - z) • deriv u x) := by abel
    nth_rewrite 1 [e]
    exact norm_sub_le (u y - u z) (u y - u z - (y - z) • deriv u x)
  rw [hs] at h2
  nlinarith [abs_nonneg (y - z), norm_nonneg (deriv u x), hpos]

/-- **Representative in `[-π, π]` modulo `2π`.**  For any `t t' : ℝ` there are `h` with `|h| ≤ π`
and `m : ℤ` with `t' = t + h + 2π m`.  (Reduce `t' - t` to `[-π, π)`.) -/
lemma exists_abs_le_pi_representative (t t' : ℝ) :
    ∃ h : ℝ, |h| ≤ Real.pi ∧ ∃ m : ℤ, t' = t + h + m * (2 * Real.pi) := by
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨toIcoMod hp (-Real.pi) (t' - t), ?_, toIcoDiv hp (-Real.pi) (t' - t), ?_⟩
  · have hm : toIcoMod hp (-Real.pi) (t' - t) ∈ Set.Ico (-Real.pi) (-Real.pi + 2 * Real.pi) :=
      toIcoMod_mem_Ico hp _ _
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hm
    exact abs_le.mpr ⟨(Set.mem_Ico.mp hm).1, le_of_lt (Set.mem_Ico.mp hm).2⟩
  · have h := self_sub_toIcoDiv_zsmul (p := 2 * Real.pi) hp (-Real.pi) (t' - t)
    simp only [zsmul_eq_mul] at h
    linarith [h]

/-- An integer multiple of `2π` whose modulus is at most `π` vanishes. -/
lemma eq_zero_of_eq_int_mul_two_pi {h : ℝ} {m : ℤ} (hm : h = m * (2 * Real.pi))
    (hπ : |h| ≤ Real.pi) : h = 0 := by
  by_contra hne
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hne hm
  have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
  have h2 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast h1
  have h3 : |h| = |(m : ℝ)| * (2 * Real.pi) := by
    rw [hm, abs_mul]
    simp [abs_of_pos Real.pi_pos, mul_comm]
  nlinarith [Real.pi_pos]

/-- **Mean value bound.**  If `δ : ℝ → ℂ` is differentiable with `‖deriv δ‖ ≤ M`, then
`‖δ (t + h) - δ t‖ ≤ M * |h|` for all `t h`. -/
lemma norm_sub_add_le_of_norm_deriv_le {δ : ℝ → ℂ} (hδ : Differentiable ℝ δ) {M : ℝ}
    (hM : ∀ t, ‖deriv δ t‖ ≤ M) (t h : ℝ) : ‖δ (t + h) - δ t‖ ≤ M * |h| := by
  have hconv : Convex ℝ (Set.Icc (min t (t + h)) (max t (t + h))) := convex_Icc _ _
  have ht : t ∈ Set.Icc (min t (t + h)) (max t (t + h)) := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht' : t + h ∈ Set.Icc (min t (t + h)) (max t (t + h)) := ⟨min_le_right _ _, le_max_right _ _⟩
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (f := δ) (C := M)
    (fun x _ => hδ x) (fun x _ => hM x) hconv ht ht'
  simpa [Real.norm_eq_abs, add_sub_cancel_left] using hmain

/-- `t` has a representative in `[0, 2π)` modulo `2π`. -/
lemma exists_mem_Ico_two_pi_representative (t : ℝ) :
    ∃ t' ∈ Set.Ico 0 (2 * Real.pi), ∃ m : ℤ, t = t' + m * (2 * Real.pi) := by
  have hp : 0 < 2 * Real.pi := by positivity
  refine ⟨toIcoMod hp 0 t, toIcoMod_mem_Ico' hp t, toIcoDiv hp 0 t, ?_⟩
  have h := self_sub_toIcoDiv_zsmul (p := 2 * Real.pi) hp 0 t
  simp only [zsmul_eq_mul] at h
  linarith [h]

/-- **Global lower Lipschitz bound for a smooth embedded loop.**  If `u : ℝ → ℂ` is `C¹`,
`2π`-periodic, injective modulo `2π` and has non-vanishing derivative, then there is `c > 0` with

`c * |h| ≤ ‖u (t + h) - u t‖`  for all `t` and all `|h| ≤ π`.

(There is *no* uniform bound over all loops: a very thin loop has a very small constant.  But for
each fixed `u` the bound holds: near the diagonal the difference quotient tends to `‖u' t‖` with a
uniform rate because `u'` is uniformly continuous on a compact neighbourhood of the fundamental
domain, while for `|h|` bounded away from `0` a minimum over a compact set of pairs together with
injectivity gives the bound.) -/
theorem loop_lower_bound_aux (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hinj : ∀ t t', u t = u t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (hreg : ∀ t, deriv u t ≠ 0) :
    ∃ c > 0, ∀ t h : ℝ, |h| ≤ Real.pi → c * |h| ≤ ‖u (t + h) - u t‖ := by
  have hcont : Continuous (deriv u) := hu.continuous_deriv le_rfl
  obtain ⟨x₀, hx₀mem, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨0, left_mem_Icc.mpr (by positivity)⟩ : (Set.Icc (0 : ℝ) (2 * Real.pi)).Nonempty)
    hcont.continuousOn.norm
  have hκpos : 0 < ‖deriv u x₀‖ := norm_pos_iff.mpr (hreg x₀)
  -- uniform continuity of `u'` on a compact neighbourhood of the fundamental domain
  have hUC : UniformContinuousOn (deriv u) (Set.Icc (-1 : ℝ) (2 * Real.pi + 1)) :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 2 * Real.pi + 1)).uniformContinuousOn_of_continuous
      hcont.continuousOn
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.uniformContinuousOn_iff_le.mp hUC (‖deriv u x₀‖ / 2) (by positivity)
  set δ : ℝ := min δ₁ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos one_pos
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδδ₁ : δ ≤ δ₁ := min_le_left _ _
  -- near-diagonal bound
  have hnear : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ z : ℝ, |z - t| ≤ δ →
      (‖deriv u x₀‖ / 2) * |z - t| ≤ ‖u z - u t‖ := by
    intro t ht z hz
    have hzt : |z - t| = max t z - min t z := by
      rcases le_total t z with h | h
      · rw [abs_of_nonneg (by linarith), max_eq_right h, min_eq_left h]
      · rw [abs_of_nonpos (by linarith), max_eq_left h, min_eq_right h]
        ring
    have hz' : max t z - min t z ≤ δ := by linarith [hzt, hz]
    have hseg : ∀ s ∈ Set.Icc (min t z) (max t z), |s - t| ≤ δ := by
      intro s hs
      have h1 : |s - t| ≤ max t z - min t z := by
        rw [abs_le]
        exact ⟨by linarith [hs.1, hs.2, min_le_left t z, le_max_left t z],
               by linarith [hs.1, hs.2, min_le_left t z, le_max_left t z]⟩
      linarith [h1, hz']
    have hderiv : ∀ s : ℝ, deriv (fun s : ℝ => u s - s • deriv u t) s = deriv u s - deriv u t := by
      intro s
      have h1 : HasDerivAt u (deriv u s) s := (hu.differentiable (by norm_num) s).hasDerivAt
      have h2 : HasDerivAt (fun y : ℝ => y • deriv u t) (deriv u t) s := by
        simpa using HasDerivAt.smul_const (hasDerivAt_id s) (deriv u t)
      exact (h1.sub h2).deriv
    have hbound : ∀ s ∈ Set.Icc (min t z) (max t z),
        ‖deriv (fun s : ℝ => u s - s • deriv u t) s‖ ≤ ‖deriv u x₀‖ / 2 := by
      intro s hs
      have hsδ : |s - t| ≤ δ := hseg s hs
      have hst : |s - t| ≤ δ₁ := le_trans hsδ hδδ₁
      have hs1 : |s - t| ≤ 1 := le_trans hsδ hδone
      rw [abs_le] at hs1
      have hsK : s ∈ Set.Icc (-1 : ℝ) (2 * Real.pi + 1) :=
        ⟨by linarith [hs1.1, ht.1], by linarith [hs1.2, ht.2]⟩
      have htK : t ∈ Set.Icc (-1 : ℝ) (2 * Real.pi + 1) :=
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have huc := hδ₁ s hsK t htK (by rw [Real.dist_eq]; exact hst)
      rw [dist_eq_norm, ← hderiv s] at huc
      exact huc
    have hdiff : ∀ s ∈ Set.Icc (min t z) (max t z),
        DifferentiableAt ℝ (fun s : ℝ => u s - s • deriv u t) s := by
      intro s _
      exact (hu.differentiable (by norm_num) s).sub
        (HasDerivAt.smul_const (hasDerivAt_id s) (deriv u t)).differentiableAt
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun s : ℝ => u s - s • deriv u t) (C := ‖deriv u x₀‖ / 2) hdiff hbound
      (convex_Icc _ _) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    have hφ : (fun s : ℝ => u s - s • deriv u t) z - (fun s : ℝ => u s - s • deriv u t) t
        = (u z - u t) - (z - t) • deriv u t := by
      simp only []
      module
    rw [hφ, Real.norm_eq_abs] at hMVT
    have htri : ‖(z - t) • deriv u t‖ ≤ ‖u z - u t‖ + ‖u z - u t - (z - t) • deriv u t‖ := by
      have e : (z - t) • deriv u t = (u z - u t) - (u z - u t - (z - t) • deriv u t) := by
        module
      nth_rewrite 1 [e]
      exact norm_sub_le (u z - u t) (u z - u t - (z - t) • deriv u t)
    have hns : ‖(z - t) • deriv u t‖ = |z - t| * ‖deriv u t‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [hns] at htri
    have hmono : ‖deriv u x₀‖ ≤ ‖deriv u t‖ := hmin ht
    nlinarith [abs_nonneg (z - t), norm_nonneg (deriv u t), hκpos]
  -- "far" pairs: compactness
  have hδπ : δ ≤ Real.pi := le_trans hδone (by linarith [Real.pi_gt_three])
  set F : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ (Set.Icc δ Real.pi ∪ Set.Icc (-Real.pi) (-δ)) with hFdef
  have hFcomp : IsCompact F := isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)
  have hFne : F.Nonempty :=
    ⟨(0, δ), ⟨⟨le_rfl, by positivity⟩, Or.inl ⟨le_rfl, hδπ⟩⟩⟩
  have habs_le : ∀ q : ℝ, q ∈ Set.Icc δ Real.pi ∪ Set.Icc (-Real.pi) (-δ) → δ ≤ |q| := by
    intro q hq
    rcases hq with h | h
    · rw [abs_of_nonneg (by linarith [h.1, hδpos])]
      exact h.1
    · rw [abs_of_nonpos (by linarith [h.2, hδpos])]
      linarith [h.2]
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => ‖u (p.1 + p.2) - u p.1‖ / |p.2|) F := by
    have hn : Continuous fun p : ℝ × ℝ => ‖u (p.1 + p.2) - u p.1‖ :=
      ((hu.continuous.comp (continuous_fst.add continuous_snd)).sub
        (hu.continuous.comp continuous_fst)).norm
    have hd : Continuous fun p : ℝ × ℝ => |p.2| := continuous_abs.comp continuous_snd
    refine hn.continuousOn.div hd.continuousOn fun p hp => ?_
    exact ne_of_gt (lt_of_lt_of_le hδpos (habs_le p.2 hp.2))
  obtain ⟨p₀, hp₀F, hp₀min⟩ := hFcomp.exists_isMinOn hFne hcontF
  have hp₀le : δ ≤ |p₀.2| := habs_le p₀.2 hp₀F.2
  have hp₀ne : p₀.2 ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hp₀le
    linarith
  have hp₀pos : 0 < ‖u (p₀.1 + p₀.2) - u p₀.1‖ / |p₀.2| := by
    have hnum : 0 < ‖u (p₀.1 + p₀.2) - u p₀.1‖ := by
      rw [norm_pos_iff]
      intro heq
      obtain ⟨m, hm⟩ := hinj p₀.1 (p₀.1 + p₀.2) (sub_eq_zero.mp heq).symm
      have hp2eq : p₀.2 = 2 * Real.pi * m := by linarith [hm]
      have hp2abs : |p₀.2| ≤ Real.pi := by
        rcases hp₀F.2 with h | h
        · exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
        · exact abs_le.mpr ⟨h.1, by linarith [h.2, Real.pi_pos]⟩
      exact hp₀ne (eq_zero_of_eq_int_mul_two_pi (h := p₀.2) (m := m)
        (by rw [hp2eq]; ring) hp2abs)
    exact div_pos hnum (lt_of_lt_of_le hδpos hp₀le)
  have hfar : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ h : ℝ, δ ≤ |h| → |h| ≤ Real.pi →
      (‖u (p₀.1 + p₀.2) - u p₀.1‖ / |p₀.2|) * |h| ≤ ‖u (t + h) - u t‖ := by
    intro t ht h hh1 hh2
    have hpF : (t, h) ∈ F := by
      refine ⟨ht, ?_⟩
      rcases le_total 0 h with h0 | h0
      · rw [abs_of_nonneg h0] at hh1 hh2
        exact Or.inl ⟨hh1, hh2⟩
      · rw [abs_of_nonpos h0] at hh1 hh2
        exact Or.inr ⟨by linarith, by linarith⟩
    have hden : 0 < |h| := lt_of_lt_of_le hδpos hh1
    exact (le_div_iff₀ hden).mp (hp₀min hpF)
  -- combine
  set c : ℝ := min (‖deriv u x₀‖ / 2) (‖u (p₀.1 + p₀.2) - u p₀.1‖ / |p₀.2|) with hcdef
  have hcpos : 0 < c := lt_min (by positivity) hp₀pos
  have hmain : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ h : ℝ, |h| ≤ Real.pi →
      c * |h| ≤ ‖u (t + h) - u t‖ := by
    intro t ht h hh
    by_cases hcase : |h| ≤ δ
    · have h1 := hnear t ht (t + h) (by rw [add_sub_cancel_left]; exact hcase)
      rw [add_sub_cancel_left] at h1
      have h2 : c ≤ ‖deriv u x₀‖ / 2 := min_le_left _ _
      have h3 : c * |h| ≤ ‖deriv u x₀‖ / 2 * |h| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg h)
      linarith
    · have hcase' : δ < |h| := not_le.mp hcase
      have h3 := hfar t ht h (le_of_lt hcase') hh
      have h2 : c ≤ ‖u (p₀.1 + p₀.2) - u p₀.1‖ / |p₀.2| := min_le_right _ _
      have h4 : c * |h| ≤ ‖u (p₀.1 + p₀.2) - u p₀.1‖ / |p₀.2| * |h| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg h)
      linarith
  -- reduce an arbitrary `t` to the fundamental domain using `2π`-periodicity
  refine ⟨c, hcpos, fun t h hh => ?_⟩
  obtain ⟨t', ht'mem, m, ht'm⟩ := exists_mem_Ico_two_pi_representative t
  have ht' : t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨(mem_Ico.mp ht'mem).1, le_of_lt (mem_Ico.mp ht'mem).2⟩
  have hpP : Function.Periodic u (2 * Real.pi) := hper
  have h1 : u (t + h) = u (t' + h) := by
    rw [ht'm]
    rw [show t' + m * (2 * Real.pi) + h = (t' + h) + m * (2 * Real.pi) by ring]
    exact hpP.int_mul m (t' + h)
  have h2 : u t = u t' := by
    rw [ht'm]
    exact hpP.int_mul m t'
  rw [h1, h2]
  exact hmain t' ht' h hh

end Work.RPB.B1a
