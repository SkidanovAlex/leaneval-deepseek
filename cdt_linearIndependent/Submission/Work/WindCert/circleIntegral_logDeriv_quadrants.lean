import Mathlib

/-!
# Winding number from a quadrant certificate: `circleIntegral_logDeriv_quadrants`

If, on each of the `n` arcs of the circle of radius `ρ` cut out by the angles
`2π i / n`, the value of `g` lies in the open half plane `{w | 0 < (w * star (u i)).re}`
with `u i ∈ {1, I, -1, -I}`, then

  ∮ (logDeriv g) = I * ∑ i, arg (u (finRotate n i) / u i).

The proof splits the circle integral into the `n` arcs, uses `Log (g/u i)` as a
holomorphic primitive on each arc (the values stay in the right half plane, hence
off the branch cut), and then telescopes; the only non-telescoping part is the
change of the argument at each corner.
-/

namespace Work.WindCert

open Complex Metric

/-! ## Elementary facts about the four units `±1, ±I` -/

lemma circleMap_add_two_pi' (c : ℂ) {R : ℝ} (hR : R ≠ 0) (θ : ℝ) :
    circleMap c R (θ + 2 * Real.pi) = circleMap c R θ :=
  (circleMap_eq_circleMap_iff c hR).mpr ⟨1, by push_cast; ring⟩

lemma div_eq_mul_star_of_mem {w u : ℂ}
    (hu : u = 1 ∨ u = Complex.I ∨ u = -1 ∨ u = -Complex.I) : w / u = w * star u := by
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp [div_eq_mul_inv, Complex.inv_I, Complex.conj_I]

lemma ne_zero_of_mem_four {u : ℂ}
    (hu : u = 1 ∨ u = Complex.I ∨ u = -1 ∨ u = -Complex.I) : u ≠ 0 := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp

lemma norm_eq_one_of_mem_four {u : ℂ}
    (hu : u = 1 ∨ u = Complex.I ∨ u = -1 ∨ u = -Complex.I) : ‖u‖ = 1 := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp

lemma star_mem_four {u : ℂ}
    (hu : u = 1 ∨ u = Complex.I ∨ u = -1 ∨ u = -Complex.I) :
    star u = 1 ∨ star u = Complex.I ∨ star u = -1 ∨ star u = -Complex.I := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inr (by simp [Complex.conj_I])))
  · exact Or.inr (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inl (by simp [Complex.conj_I]))

lemma mul_mem_four {x y : ℂ}
    (hx : x = 1 ∨ x = Complex.I ∨ x = -1 ∨ x = -Complex.I)
    (hy : y = 1 ∨ y = Complex.I ∨ y = -1 ∨ y = -Complex.I) :
    x * y = 1 ∨ x * y = Complex.I ∨ x * y = -1 ∨ x * y = -Complex.I := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [Complex.I_mul_I]

lemma abs_arg_le_pi_div_two_of_mem {c : ℂ}
    (hc : c = 1 ∨ c = Complex.I ∨ c = -1 ∨ c = -Complex.I) (hne : c ≠ -1) :
    |Complex.arg c| ≤ Real.pi / 2 := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp only [Complex.arg_one, abs_zero]; positivity
  · rw [Complex.arg_I, abs_of_nonneg (by positivity)]
  · exact absurd rfl hne
  · rw [Complex.arg_neg_I, abs_neg, abs_of_nonneg (by positivity)]

lemma log_eq_mul_I_arg (z : ℂ) (hz : ‖z‖ = 1) :
    Complex.log z = Complex.I * (Complex.arg z : ℂ) := by
  have h1 : Complex.log z = ((Real.log ‖z‖ : ℝ) : ℂ) + (Complex.arg z : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  rw [h1, hz, Real.log_one, Complex.ofReal_zero, zero_add, mul_comm]

/-! ## The corner relation -/

lemma log_div_sub_log_div_eq_arg_mul_I {w u v : ℂ}
    (hu : u = 1 ∨ u = Complex.I ∨ u = -1 ∨ u = -Complex.I)
    (hv : v = 1 ∨ v = Complex.I ∨ v = -1 ∨ v = -Complex.I)
    (hvu : v ≠ -u) (huw : 0 < (w / u).re) (hvw : 0 < (w / v).re) :
    Complex.log (w / u) - Complex.log (w / v) = Complex.I * (Complex.arg (v / u) : ℂ) := by
  have hu0 : u ≠ 0 := ne_zero_of_mem_four hu
  have hv0 : v ≠ 0 := ne_zero_of_mem_four hv
  have hun : ‖u‖ = 1 := norm_eq_one_of_mem_four hu
  have hvn : ‖v‖ = 1 := norm_eq_one_of_mem_four hv
  have hcn : ‖v / u‖ = 1 := by rw [norm_div, hvn, hun, div_one]
  have hcne : v / u ≠ -1 := by
    intro h
    refine hvu ?_
    have h2 : v / u * u = (-1) * u := by rw [h]
    rw [div_mul_cancel₀ v hu0, neg_one_mul] at h2
    exact h2
  have hcm : v / u = 1 ∨ v / u = Complex.I ∨ v / u = -1 ∨ v / u = -Complex.I := by
    rw [div_eq_mul_star_of_mem hu]
    exact mul_mem_four hv (star_mem_four hu)
  have hargc : |Complex.arg (v / u)| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_of_mem hcm hcne
  have hlogc : Complex.log (v / u) = Complex.I * (Complex.arg (v / u) : ℂ) :=
    log_eq_mul_I_arg _ hcn
  have hB : w / v ≠ 0 := by
    intro h; rw [h] at hvw; simp at hvw
  have hargB : |Complex.arg (w / v)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hvw)
  have hIoc : Complex.arg (w / v) + Complex.arg (v / u) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 : -(Real.pi / 2) < Complex.arg (w / v) := (abs_lt.mp hargB).1
    have h2 : Complex.arg (w / v) < Real.pi / 2 := (abs_lt.mp hargB).2
    have h3 : -(Real.pi / 2) ≤ Complex.arg (v / u) := by
      have := neg_abs_le (Complex.arg (v / u)); linarith
    have h4 : Complex.arg (v / u) ≤ Real.pi / 2 := by
      have := le_abs_self (Complex.arg (v / u)); linarith
    exact ⟨by linarith, by linarith⟩
  have hkey : Complex.log (w / u) = Complex.log (w / v) + Complex.log (v / u) := by
    have hmul : w / u = (w / v) * (v / u) := by field_simp
    rw [hmul, Complex.log_mul hB (div_ne_zero hv0 hu0) hIoc]
  rw [hkey, hlogc]
  ring

/-! ## The primitive on one arc -/

theorem intervalIntegral_circleMap_logDeriv_eq_log_sub {g : ℂ → ℂ} {R ρ a b : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < R) (hab : a ≤ b) (hg : AnalyticOnNhd ℂ g (Metric.ball 0 R)) {u : ℂ}
    (hu : u = 1 ∨ u = Complex.I ∨ u = -1 ∨ u = -Complex.I)
    (harc : ∀ t ∈ Set.Icc a b, 0 < (g (circleMap 0 ρ t) * star u).re) :
    IntervalIntegrable (fun t => deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t))
        MeasureTheory.volume a b ∧
      ∫ t in a..b, deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t) =
        Complex.log (g (circleMap 0 ρ b) / u) - Complex.log (g (circleMap 0 ρ a) / u) := by
  have hu0 : u ≠ 0 := ne_zero_of_mem_four hu
  have hmem : ∀ t : ℝ, circleMap 0 ρ t ∈ Metric.ball 0 R := by
    intro t
    have h := circleMap_mem_sphere' (0 : ℂ) ρ t
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos hρ] at h
    rw [Metric.mem_ball, dist_zero_right, h]
    exact hρR
  have hdg : ∀ t : ℝ, HasDerivAt g (deriv g (circleMap 0 ρ t)) (circleMap 0 ρ t) := fun t =>
    ((hg (circleMap 0 ρ t) (hmem t)).differentiableAt).hasDerivAt
  have hre : ∀ t ∈ Set.Icc a b, 0 < (g (circleMap 0 ρ t) / u).re := by
    intro t ht
    rw [div_eq_mul_star_of_mem hu]
    exact harc t ht
  have hne : ∀ t ∈ Set.Icc a b, g (circleMap 0 ρ t) ≠ 0 := by
    intro t ht h
    have := hre t ht
    rw [h, zero_div] at this
    exact lt_irrefl 0 this
  set Φ : ℝ → ℂ := fun t => Complex.log (g (circleMap 0 ρ t) / u) with hΦ
  have hder : ∀ t ∈ Set.Ioo a b,
      HasDerivAt Φ (deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t)) t := by
    intro t ht
    have htI : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    have hslit : g (circleMap 0 ρ t) / u ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (hre t htI)
    have h1 : HasDerivAt (fun s => g (circleMap 0 ρ s) / u)
        ((deriv g (circleMap 0 ρ t) * (circleMap 0 ρ t * Complex.I)) / u) t :=
      ((hdg t).comp t (hasDerivAt_circleMap 0 ρ t)).div_const u
    have h2 := (Complex.hasDerivAt_log hslit).comp t h1
    have h3 : (g (circleMap 0 ρ t) / u)⁻¹ *
        ((deriv g (circleMap 0 ρ t) * (circleMap 0 ρ t * Complex.I)) / u)
        = deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t) := by
      rw [logDeriv_apply, deriv_circleMap]
      field_simp
    rw [hΦ]
    exact h2.congr_deriv h3
  have hcont : ContinuousOn Φ (Set.Icc a b) := by
    rw [hΦ]
    refine ContinuousOn.clog ?_ ?_
    · refine ContinuousOn.div ?_ continuousOn_const ?_
      · exact hg.continuousOn.comp (continuous_circleMap 0 ρ).continuousOn (fun t _ => hmem t)
      · intro t ht
        exact hu0
    · intro t ht
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (hre t ht)
  have hint : IntervalIntegrable
      (fun t => deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t))
      MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine ContinuousOn.mul ?_ ?_
    · have hder' : deriv (circleMap 0 ρ) = fun t => circleMap 0 ρ t * Complex.I :=
        funext fun t => deriv_circleMap 0 ρ t
      rw [hder']
      exact ((continuous_circleMap 0 ρ).mul continuous_const).continuousOn
    · have hdgcont : ContinuousOn (deriv g) (Metric.ball 0 R) :=
        (hg.deriv_of_isOpen Metric.isOpen_ball).continuousOn
      have h1 : ContinuousOn (fun t => deriv g (circleMap 0 ρ t)) (Set.Icc a b) :=
        hdgcont.comp (continuous_circleMap 0 ρ).continuousOn (fun t _ => hmem t)
      have h2 : ContinuousOn (fun t => g (circleMap 0 ρ t)) (Set.Icc a b) :=
        hg.continuousOn.comp (continuous_circleMap 0 ρ).continuousOn (fun t _ => hmem t)
      have h3 : (fun t => logDeriv g (circleMap 0 ρ t))
          = fun t => deriv g (circleMap 0 ρ t) / g (circleMap 0 ρ t) := by
        funext t; rw [logDeriv_apply]
      rw [h3]
      exact h1.div h2 (fun t ht => hne t ht)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hder hint⟩

/-! ## The main theorem -/

theorem circleIntegral_logDeriv_quadrants {g : ℂ → ℂ} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (n : ℕ) (hn : 0 < n) (u : Fin n → ℂ)
    (hu : ∀ i, u i = 1 ∨ u i = Complex.I ∨ u i = -1 ∨ u i = -Complex.I)
    (harc : ∀ i : Fin n, ∀ t ∈ Set.Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n),
      0 < (g (circleMap 0 ρ (2 * Real.pi * t)) * star (u i)).re) :
    circleIntegral (fun z => logDeriv g z) 0 ρ =
      Complex.I * ∑ i : Fin n, (Complex.arg (u (finRotate n i) / u i) : ℂ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hR0 : ρ ≠ 0 := hρ.ne'
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pne : (2 : ℝ) * Real.pi ≠ 0 := h2pi.ne'
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set A : ℕ → ℝ := fun k => 2 * Real.pi * (k : ℝ) / ((m : ℝ) + 1) with hA
  have harc' : ∀ i : Fin (m + 1),
      ∀ t ∈ Set.Icc ((i : ℝ) / ((m : ℝ) + 1)) (((i : ℝ) + 1) / ((m : ℝ) + 1)),
        0 < (g (circleMap 0 ρ (2 * Real.pi * t)) * star (u i)).re := by
    intro i t ht
    exact harc i t (by push_cast; exact ht)
  have haleN : ∀ k (hk : k < m + 1), A k ≤ A (k + 1) := by
    intro k hk
    simp only [hA]
    push_cast
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hden.le
  have harcN : ∀ k (hk : k < m + 1), ∀ t ∈ Set.Icc (A k) (A (k + 1)),
      0 < (g (circleMap 0 ρ t) * star (u ⟨k, hk⟩)).re := by
    intro k hk t ht
    have ht1 : A k ≤ t := ht.1
    have ht2 : t ≤ A (k + 1) := ht.2
    simp only [hA] at ht1 ht2
    push_cast at ht1 ht2
    have hs : t / (2 * Real.pi)
        ∈ Set.Icc (((⟨k, hk⟩ : Fin (m + 1)) : ℝ) / ((m : ℝ) + 1))
            ((((⟨k, hk⟩ : Fin (m + 1)) : ℝ) + 1) / ((m : ℝ) + 1)) := by
      constructor
      · rw [le_div_iff₀ h2pi, Fin.val_mk]
        calc ((k : ℝ) / ((m : ℝ) + 1)) * (2 * Real.pi)
            = 2 * Real.pi * (k : ℝ) / ((m : ℝ) + 1) := by ring
          _ ≤ t := ht1
      · rw [div_le_iff₀ h2pi, Fin.val_mk]
        calc t ≤ 2 * Real.pi * ((k : ℝ) + 1) / ((m : ℝ) + 1) := ht2
          _ = (((k : ℝ) + 1) / ((m : ℝ) + 1)) * (2 * Real.pi) := by ring
    have h := harc' ⟨k, hk⟩ (t / (2 * Real.pi)) hs
    have htw : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rwa [htw] at h
  have hsplit : ∫ θ in 0..2 * Real.pi, deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ)
      = ∑ k ∈ Finset.range (m + 1),
          ∫ θ in A k..A (k + 1), deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ) := by
    have h0 : A 0 = 0 := by simp [hA]
    have hlast : A (m + 1) = 2 * Real.pi := by
      simp only [hA]
      rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
      field_simp
    have hint : ∀ k < m + 1, IntervalIntegrable
        (fun t => deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t))
        MeasureTheory.volume (A k) (A (k + 1)) :=
      fun k hk => (intervalIntegral_circleMap_logDeriv_eq_log_sub hρ hρR (haleN k hk) hg
        (hu ⟨k, hk⟩) (harcN k hk)).1
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun t => deriv (circleMap 0 ρ) t * logDeriv g (circleMap 0 ρ t))
      (a := A) (n := m + 1) hint
    rw [h0, hlast] at h
    exact h.symm
  have hsplitFin : ∫ θ in 0..2 * Real.pi, deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ)
      = ∑ i : Fin (m + 1),
          ∫ θ in A (i : ℕ)..A ((i : ℕ) + 1),
            deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ) := by
    rw [hsplit]
    exact (Fin.sum_univ_eq_sum_range
      (fun k => ∫ θ in A k..A (k + 1), deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ))
      (m + 1)).symm
  set Z : Fin (m + 1) → ℂ :=
    fun i => Complex.log (g (circleMap 0 ρ (A (i : ℕ))) / u i) with hZ
  have hpieceFin : ∀ i : Fin (m + 1),
      ∫ θ in A (i : ℕ)..A ((i : ℕ) + 1), deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ)
        = Complex.log (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i) - Z i := by
    intro i
    rw [hZ]
    exact (intervalIntegral_circleMap_logDeriv_eq_log_sub hρ hρR (haleN i.val i.isLt) hg
      (hu i) (harcN i.val i.isLt)).2
  have hArcSum : ∑ i : Fin (m + 1),
        ∫ θ in A (i : ℕ)..A ((i : ℕ) + 1),
          deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ)
      = ∑ i : Fin (m + 1),
          (Complex.log (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i) - Z i) :=
    Finset.sum_congr rfl (fun i _ => hpieceFin i)
  have htel : ∑ i : Fin (m + 1),
        (Complex.log (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i) - Z i)
      = Complex.I * ∑ i : Fin (m + 1),
          (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ) := by
    have hpt : ∀ i : Fin (m + 1),
        circleMap 0 ρ (A ((i : ℕ) + 1))
          = circleMap 0 ρ (A (((finRotate (m + 1) i : Fin (m + 1)) : ℕ))) := by
      intro i
      rcases lt_or_ge (i : ℕ) m with hlt | hge
      · have hrot : (((finRotate (m + 1) i : Fin (m + 1)) : ℕ)) = (i : ℕ) + 1 := by
          have := congr_arg Fin.val (finRotate_of_lt (n := m) hlt)
          simpa using this
        rw [hrot]
      · have hrot : (((finRotate (m + 1) i : Fin (m + 1)) : ℕ)) = 0 := by
          have hi : i = Fin.last m := Fin.ext (by simp; omega)
          rw [hi, finRotate_last]
          rfl
        rw [hrot]
        have hi1 : (i : ℕ) + 1 = m + 1 := by omega
        rw [hi1]
        have h1 : A (m + 1) = 2 * Real.pi := by
          simp only [hA]
          rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
          field_simp
        have h0 : A 0 = 0 := by simp [hA]
        rw [h1, h0]
        simpa using circleMap_add_two_pi' (0 : ℂ) hR0 0
    have hkey : ∀ i : Fin (m + 1),
        Complex.log (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i)
          = Z (finRotate (m + 1) i)
            + Complex.I * (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ) := by
      intro i
      have h1 : 0 < (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i).re := by
        have hh := harc' i (((i : ℝ) + 1) / ((m : ℝ) + 1))
          ⟨div_le_div_of_nonneg_right (by linarith) hden.le, le_refl _⟩
        have h2 : 2 * Real.pi * (((i : ℝ) + 1) / ((m : ℝ) + 1)) = A ((i : ℕ) + 1) := by
          simp only [hA]; push_cast; ring
        rw [h2] at hh
        rwa [← div_eq_mul_star_of_mem (hu i)] at hh
      have h2 : 0 < (g (circleMap 0 ρ (A ((i : ℕ) + 1)))
          / u (finRotate (m + 1) i)).re := by
        have hh := harc' (finRotate (m + 1) i)
          ((((finRotate (m + 1) i : Fin (m + 1)) : ℕ) : ℝ) / ((m : ℝ) + 1))
          ⟨le_refl _, div_le_div_of_nonneg_right (by linarith) hden.le⟩
        have h3 : 2 * Real.pi * ((((finRotate (m + 1) i : Fin (m + 1)) : ℕ) : ℝ) / ((m : ℝ) + 1))
            = A (((finRotate (m + 1) i : Fin (m + 1)) : ℕ)) := by
          simp only [hA]; push_cast; ring
        rw [h3, ← hpt i] at hh
        rwa [← div_eq_mul_star_of_mem (hu (finRotate (m + 1) i))] at hh
      have h3 : u (finRotate (m + 1) i) ≠ -(u i) := by
        intro hvu
        have hneg : g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u (finRotate (m + 1) i)
            = -(g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i) := by
          rw [hvu, div_neg]
        rw [hneg, Complex.neg_re] at h2
        linarith
      have hkey := log_div_sub_log_div_eq_arg_mul_I (hu i) (hu (finRotate (m + 1) i)) h3 h1 h2
      rw [hpt i, sub_eq_iff_eq_add] at hkey
      calc Complex.log (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i)
          = Complex.log (g (circleMap 0 ρ (A (((finRotate (m + 1) i : Fin (m + 1)) : ℕ)))) / u i) := by
            rw [hpt i]
        _ = Complex.log (g (circleMap 0 ρ (A (((finRotate (m + 1) i : Fin (m + 1)) : ℕ))))
              / u (finRotate (m + 1) i))
              + Complex.I * (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ) := by
            rw [hkey, add_comm]
        _ = Z (finRotate (m + 1) i)
              + Complex.I * (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ) := by rw [hZ]
    have hperm : ∑ i : Fin (m + 1), Z (finRotate (m + 1) i) = ∑ i : Fin (m + 1), Z i := by
      simpa using Equiv.Perm.sum_comp (finRotate (m + 1)) (Finset.univ : Finset (Fin (m + 1)))
        Z (by intro a _; simp)
    calc ∑ i : Fin (m + 1),
          (Complex.log (g (circleMap 0 ρ (A ((i : ℕ) + 1))) / u i) - Z i)
        = ∑ i : Fin (m + 1),
            ((Z (finRotate (m + 1) i)
              + Complex.I * (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ)) + -Z i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hkey i]
          ring
      _ = ∑ i : Fin (m + 1),
            (Complex.I * (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, hperm]
          abel
      _ = Complex.I * ∑ i : Fin (m + 1),
            (Complex.arg (u (finRotate (m + 1) i) / u i) : ℂ) := by
          rw [Finset.mul_sum]
  have hci : circleIntegral (fun z => logDeriv g z) 0 ρ
      = ∫ θ in 0..2 * Real.pi, deriv (circleMap 0 ρ) θ * logDeriv g (circleMap 0 ρ θ) := by
    simp only [circleIntegral, smul_eq_mul]
  rw [hci, hsplitFin, hArcSum, htel]

end Work.WindCert
