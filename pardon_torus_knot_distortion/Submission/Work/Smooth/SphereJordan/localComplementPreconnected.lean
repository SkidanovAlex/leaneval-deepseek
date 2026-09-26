import Mathlib
import Submission.Work.Smooth.SphereJordan.localSliceArc
import Submission.Work.Smooth.SphereJordan.localComplementBasic

namespace Work.Smooth.SphereJordan

open Set Metric

/-- Rotating the direction `u'` by a unit `ustar` leaves its pairing with `w - x` unchanged
(the key computation that identifies the local complement with the rotated slices). -/
theorem re_star_mul_rotate (ustar u' w x : ℂ) :
    (star (ustar * u') * (w - x)).re = (star u' * (star ustar * (w - x))).re := by
  rw [star_mul, mul_assoc]

/-- The converse of `re_star_mul_rotate`: undoing the rotation (with `ustar * star ustar = 1`)
returns the original pairing. -/
theorem re_star_rotate_converse {ustar u w x : ℂ} (hu : ustar * star ustar = 1) :
    (star (star ustar * u) * (star ustar * (w - x))).re = (star u * (w - x)).re := by
  rw [star_mul, star_star, mul_assoc (star u) ustar (star ustar * (w - x)),
      ← mul_assoc ustar (star ustar) (w - x), hu, one_mul]

theorem localComplementPreconnected {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r))
    (hgen : ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ w ∈ Q, dist x w = r → (star u * (w - x)).re < 0) :
    ∃ ε > 0, IsPreconnected (((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) ∩ Metric.ball x ε) := by
  classical
  obtain ⟨ε₁, hε₁pos, hε₁eq⟩ := localComplement_eq Q hr hx
  obtain ⟨ustar, hustar_norm, hustar_cond⟩ := hgen
  obtain ⟨w0, hw0Q, hw0r⟩ := active_nonempty hx
  have hu1 : ustar * star ustar = 1 := by
    have h1 := RCLike.mul_conj ustar
    rw [hustar_norm] at h1
    norm_num at h1
    exact h1
  let act : Finset ℂ := Q.filter (fun w => dist x w = r)
  have hw0act : w0 ∈ act := Finset.mem_filter.mpr ⟨hw0Q, hw0r⟩
  haveI : Nonempty ↥act := ⟨⟨w0, hw0act⟩⟩
  let v : ↥act → ℂ := fun i => star ustar * (i.val - x)
  have hmem : ∀ i : ↥act, i.val ∈ Q ∧ dist x i.val = r := fun i =>
    Finset.mem_filter.mp (show i.val ∈ Q.filter (fun w => dist x w = r) from i.property)
  have hv : ∀ i : ↥act, ‖v i‖ = r := by
    intro i
    have hi : dist x i.val = r := (hmem i).2
    dsimp only [v]
    rw [norm_mul, norm_star, hustar_norm, one_mul]
    rw [dist_eq_norm, norm_sub_rev] at hi
    exact hi
  have hfree : ∀ i : ↥act, (v i).re < 0 := by
    intro i
    show (star ustar * (i.val - x)).re < 0
    exact hustar_cond i.val (hmem i).1 (hmem i).2
  obtain ⟨c, hcpos, hc⟩ := slice_isArc v hr hv hfree
  set ε : ℝ := min ε₁ (2 * c) with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos (by linarith)
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hε2c : ε ≤ 2 * c := min_le_right _ _
  -- The local-complement description at the (smaller) radius `ε`.
  have hEdesc : ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) ∩ Metric.ball x ε =
      {y : ℂ | ∃ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 ∧ 0 < ρ ∧ ρ < ε ∧ y = x + ρ * u ∧
        ∀ w ∈ Q, dist x w = r → 2 * (star u * (w - x)).re < ρ} := by
    ext y
    constructor
    · intro hy
      have hy1 : y ∈ ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) ∩ Metric.ball x ε₁ :=
        ⟨hy.1, Metric.ball_subset_ball hεε₁ hy.2⟩
      rw [hε₁eq] at hy1
      obtain ⟨u, ρ, hu, hρ0, hρ1, hyx, hcond⟩ := hy1
      have hyb : y ∈ Metric.ball x ε := hy.2
      rw [Metric.mem_ball, dist_eq_norm] at hyb
      rw [hyx, add_sub_cancel_left, norm_mul, hu, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ0] at hyb
      exact ⟨u, ρ, hu, hρ0, hyb, hyx, hcond⟩
    · rintro ⟨u, ρ, hu, hρ0, hρε, hyx, hcond⟩
      have hy1 : y ∈ ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) ∩ Metric.ball x ε₁ := by
        rw [hε₁eq]
        exact ⟨u, ρ, hu, hρ0, lt_of_lt_of_le hρε hεε₁, hyx, hcond⟩
      refine ⟨hy1.1, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm, hyx, add_sub_cancel_left, norm_mul, hu,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
      exact hρε
  -- The rotated slices, the radial spine, and the index type of radii.
  let slice : ℝ → Set ℂ := fun c' => {u : ℂ | ‖u‖ = 1 ∧ ∀ i : ↥act, (star u * v i).re < c'}
  let Sp : ℝ → Set ℂ :=
    fun ρ => {y : ℂ | ∃ u' : ℂ, u' ∈ slice (ρ / 2) ∧ x + ρ * (ustar * u') = y}
  let R : Set ℂ := {y : ℂ | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) ε ∧ x + t * ustar = y}
  have hsliceArc : ∀ c' ∈ Set.Ioo (0 : ℝ) c, IsPreconnected (slice c') := by
    intro c' hc'
    obtain ⟨a, b, hab, hb, hseq⟩ := hc c' hc'
    have hsq : slice c' = (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Set.Ioo a b := by
      have h1 : slice c' = {u : ℂ | ‖u‖ = 1 ∧ ∀ i : ↥act, (star u * v i).re < c'} := rfl
      rw [h1, hseq]
      rfl
    rw [hsq]
    exact isPreconnected_Ioo.image _ (by fun_prop)
  have hSpArc : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε, IsPreconnected (Sp ρ) := by
    intro ρ hρ
    have hρc : ρ / 2 ∈ Set.Ioo (0 : ℝ) c := by
      refine ⟨by linarith [hρ.1], ?_⟩
      have h2 : ρ < 2 * c := lt_of_lt_of_le hρ.2 hε2c
      linarith
    exact (hsliceArc (ρ / 2) hρc).image _ (by fun_prop)
  have hRArc : IsPreconnected R := isPreconnected_Ioo.image _ (by fun_prop)
  have hpoint : (⋂ i : Set.Ioo (0 : ℝ) ε, (Sp i.val ∪ R)).Nonempty := by
    refine ⟨(fun t : ℝ => x + t * ustar) (ε / 2), ?_⟩
    rw [Set.mem_iInter]
    intro i
    right
    exact ⟨ε / 2, ⟨by linarith [hεpos], by linarith [hεpos]⟩, rfl⟩
  have hunion : IsPreconnected (⋃ i : Set.Ioo (0 : ℝ) ε, (Sp i.val ∪ R)) := by
    apply isPreconnected_iUnion hpoint
    intro i
    refine IsPreconnected.union (x + i.val * (ustar * 1)) ?_ ?_ (hSpArc i.val i.property) hRArc
    · refine ⟨1, ?_, rfl⟩
      refine ⟨norm_one, ?_⟩
      intro j
      have hj := hfree j
      simp only [star_one, one_mul]
      have h2 : 0 < i.val / 2 := by linarith [i.property.1]
      linarith
    · exact ⟨i.val, i.property, by rw [mul_one]⟩
  have hEY : ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) ∩ Metric.ball x ε =
      ⋃ i : Set.Ioo (0 : ℝ) ε, (Sp i.val ∪ R) := by
    rw [hEdesc]
    ext y
    constructor
    · rintro ⟨u, ρ, hu, hρ0, hρε, hyx, hcond⟩
      have hu'norm : ‖star ustar * u‖ = 1 := by
        rw [norm_mul, norm_star, hustar_norm, hu, one_mul]
      have hu'slice : star ustar * u ∈ slice (ρ / 2) := by
        refine ⟨hu'norm, ?_⟩
        intro j
        have hlt := hcond j.val (hmem j).1 (hmem j).2
        have hid := re_star_rotate_converse (ustar := ustar) (u := u) (w := j.val) (x := x) hu1
        show (star (star ustar * u) * v j).re < ρ / 2
        rw [show v j = star ustar * (j.val - x) from rfl, hid]
        linarith
      refine Set.mem_iUnion.mpr ⟨⟨ρ, ⟨hρ0, hρε⟩⟩, ?_⟩
      show y ∈ Sp ρ ∪ R
      left
      refine ⟨star ustar * u, hu'slice, ?_⟩
      have huu : ustar * (star ustar * u) = u := by rw [← mul_assoc, hu1, one_mul]
      show x + ρ * (ustar * (star ustar * u)) = y
      rw [huu, hyx]
    · intro hy
      rcases Set.mem_iUnion.mp hy with ⟨i, hi | hi⟩
      · have hhi : ∃ u' : ℂ, u' ∈ slice (i.val / 2) ∧ x + i.val * (ustar * u') = y := hi
        rcases hhi with ⟨u', hu'slice, hu'eq⟩
        rw [← hu'eq]
        refine ⟨ustar * u', i.val, ?_, i.property.1, i.property.2, rfl, ?_⟩
        · rw [norm_mul, hu'slice.1, mul_one, hustar_norm]
        · intro w hwQ hwr
          have hlt := hu'slice.2 ⟨w, Finset.mem_filter.mpr ⟨hwQ, hwr⟩⟩
          rw [show v ⟨w, Finset.mem_filter.mpr ⟨hwQ, hwr⟩⟩ = star ustar * (w - x) from rfl] at hlt
          rw [re_star_mul_rotate]
          linarith
      · have hhi : ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) ε ∧ x + t * ustar = y := hi
        rcases hhi with ⟨t, ht, ht_eq⟩
        rw [← ht_eq]
        refine ⟨ustar, t, hustar_norm, ht.1, ht.2, rfl, ?_⟩
        · intro w hwQ hwr
          have h := hustar_cond w hwQ hwr
          linarith [ht.1]
  exact ⟨ε, hεpos, by rw [hEY]; exact hunion⟩

end Work.Smooth.SphereJordan
