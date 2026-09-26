import Mathlib

/-!
# The local geometry of the frontier of a finite union of equal closed discs

At a frontier point `z` of `S = ⋃_{w ∈ P} closedBall w r` there is a *unit direction* `w` which is
**not covered** by the discs: `Re (star w * (v - z)) ≤ 0` for every centre `v` with `dist z v = r`.
This is the local structure of the complement of `interior S` at `z`.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

variable {P : Finset ℂ} {r : ℝ}

/-- The union of the closed balls. -/
def ballU (P : Finset ℂ) (r : ℝ) : Set ℂ := ⋃ w ∈ P, Metric.closedBall w r

theorem isClosed_ballU (P : Finset ℂ) (r : ℝ) : IsClosed (ballU P r) :=
  isClosed_biUnion_finset fun _ _ => Metric.isClosed_closedBall

theorem mem_ballU {z : ℂ} : z ∈ ballU P r ↔ ∃ w ∈ P, z ∈ Metric.closedBall w r := by
  simp [ballU]

theorem norm_div_norm_self (y : ℂ) (hy : y ≠ 0) : ‖y / (‖y‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y),
    div_self (ne_of_gt (norm_pos_iff.mpr hy))]

/-- The inner product identity behind the local structure. -/
theorem norm_sq_sub_eq (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (star a * b).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_sub]
  simp [Complex.mul_re]

/-- **A direction covered by the discs forces an interior point.** -/
theorem interior_of_covered_directions {z : ℂ} (hr : 0 < r)
    (hcov : ∀ w' : ℂ, ‖w'‖ = 1 → ∃ v ∈ P, dist z v = r ∧ 0 < (star w' * (v - z)).re) :
    z ∈ interior (ballU P r) := by
  set Q : Finset ℂ := P.filter (fun v => dist z v = r) with hQ
  have hQmem : ∀ v, v ∈ Q ↔ v ∈ P ∧ dist z v = r := by intro v; simp [hQ]
  have hQne : Q.Nonempty := by
    obtain ⟨v, hvP, hv, _⟩ := hcov 1 (by simp)
    exact ⟨v, (hQmem v).mpr ⟨hvP, hv⟩⟩
  set g : ℂ → ℝ := fun w' => Q.sup' hQne (fun v => (star w' * (v - z)).re) with hg
  have hge_g : ∀ w', g w' = Q.sup' hQne (fun v => (star w' * (v - z)).re) := by
    intro w'; rw [hg]
  have hgc : Continuous g := by
    rw [hg]
    have h := Continuous.finset_sup' (s := Q) hQne
      (f := fun v (w' : ℂ) => (star w' * (v - z)).re)
      (fun v _ => Complex.continuous_re.comp
        ((continuous_star.comp continuous_id).mul continuous_const))
    have heta : (fun w' : ℂ => Q.sup' hQne (fun v => (star w' * (v - z)).re)) =
        (Q.sup' hQne (fun v (w' : ℂ) => (star w' * (v - z)).re)) := by
      funext w'
      exact (Finset.sup'_apply hQne (fun v (w' : ℂ) => (star w' * (v - z)).re) w').symm
    rw [heta]; exact h
  have hpos : ∀ w', ‖w'‖ = 1 → 0 < g w' := by
    intro w' hw'
    obtain ⟨v, hvP, hv, hvpos⟩ := hcov w' hw'
    have hvQ : v ∈ Q := (hQmem v).mpr ⟨hvP, hv⟩
    rw [hge_g]
    exact lt_of_lt_of_le hvpos (Finset.le_sup' (fun v => (star w' * (v - z)).re) hvQ)
  have hsc : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hsne : (Metric.sphere (0 : ℂ) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := hsc.exists_isMinOn hsne hgc.continuousOn
  have hgw₀ : 0 < g w₀ := hpos w₀ (by simpa using hw₀mem)
  have hzS : z ∈ ballU P r := by
    obtain ⟨v, hvP, hv, _⟩ := hcov 1 (by simp)
    exact mem_ballU.mpr ⟨v, hvP, Metric.mem_closedBall.mpr (le_of_eq hv)⟩
  refine mem_interior_iff_mem_nhds.mpr
    (Metric.mem_nhds_iff.mpr ⟨min (g w₀) 1 / 2, by positivity, ?_⟩)
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  by_cases hyz : y - z = 0
  · rw [show y = z from sub_eq_zero.mp hyz]; exact hzS
  · set w' : ℂ := (y - z) / (‖y - z‖ : ℂ) with hw'
    have hw'norm : ‖w'‖ = 1 := by rw [hw']; exact norm_div_norm_self _ hyz
    have hgw' : g w₀ ≤ g w' := hw₀min (Metric.mem_sphere.mpr (by simpa using hw'norm))
    obtain ⟨v, hvQ, hveq⟩ := Finset.exists_mem_eq_sup' hQne
      (fun v => (star w' * (v - z)).re)
    have hvP : v ∈ P := (hQmem v).mp hvQ |>.1
    have hvz : dist z v = r := (hQmem v).mp hvQ |>.2
    have hvge : g w₀ ≤ (star w' * (v - z)).re := by
      rw [hge_g w'] at hgw'
      exact le_trans hgw' hveq.le
    have hystar : star (y - z) * (v - z) = (‖y - z‖ : ℂ) * (star w' * (v - z)) := by
      have hc : star ((‖y - z‖ : ℝ) : ℂ) = ((‖y - z‖ : ℝ) : ℂ) := Complex.conj_ofReal _
      rw [hw', star_div₀, hc]
      have hne : ((‖y - z‖ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hyz))
      field_simp
    have hmem : y ∈ Metric.closedBall v r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hb : ‖v - z‖ = r := by rw [← dist_eq_norm, dist_comm]; exact hvz
      have hre : (star (y - z) * (v - z)).re = ‖y - z‖ * (star w' * (v - z)).re := by
        rw [hystar, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hylμ : ‖y - z‖ < g w₀ := by
        have h1 : min (g w₀) 1 / 2 ≤ g w₀ := by
          have h2 := min_le_left (g w₀) 1
          linarith
        linarith
      have hposy : 0 < ‖y - z‖ := norm_pos_iff.mpr hyz
      have hsq : ‖y - v‖ ^ 2 < r ^ 2 := by
        rw [show y - v = (y - z) - (v - z) by ring, norm_sq_sub_eq, hb, hre]
        nlinarith [hylμ, hvge, hgw₀, hposy, hr]
      nlinarith [norm_nonneg (y - v), hr]
    exact mem_ballU.mpr ⟨v, hvP, hmem⟩

/-- **At a frontier point some direction is uncovered.** -/
theorem exists_uncovered_direction {z : ℂ} (hr : 0 < r) (hz : z ∈ frontier (ballU P r)) :
    ∃ w' : ℂ, ‖w'‖ = 1 ∧ ∀ v ∈ P, dist z v = r → (star w' * (v - z)).re ≤ 0 := by
  by_contra h
  rw [not_exists] at h
  push Not at h
  exact hz.2 (interior_of_covered_directions hr fun w' hw' => h w' hw')

end

end Work.Smooth.SphereJordan
