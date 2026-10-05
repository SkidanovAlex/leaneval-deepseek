import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_max_dist_pair
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_bounded_component_of_homeomorph
import Submission.Work.RPB1a.Caratheodory.Brouwer.isBounded_image_affine

namespace Work.RPB1a.Caratheodory.Brouwer

/-- **The "lens" computation.**  If the point `s` of the plane lies in the lens
`{s | ‖s + 1‖ ≤ 2 ∧ ‖s - 1‖ ≤ 2}` (the intersection of the two discs of radius `2` centred at `-1`
and `1`), then `s` lies in the rectangle `[-1,1] × [-2,2]`; moreover, if one of its coordinates is
one of the four boundary values `-1, 1, -2, 2`, then `s` must be one of the two cut points `±1`. -/
theorem lens_mem_rect_of_norm_le_two (s : ℂ) (h1 : ‖s + 1‖ ≤ 2) (h2 : ‖s - 1‖ ≤ 2) :
    -1 ≤ s.re ∧ s.re ≤ 1 ∧ -2 ≤ s.im ∧ s.im ≤ 2 ∧
      ((s.re = -1 ∨ s.re = 1 ∨ s.im = -2 ∨ s.im = 2) → s = -1 ∨ s = 1) := by
  have hs1 : (s.re + 1)^2 + s.im^2 ≤ 4 := by
    have h : Complex.normSq (s + 1) ≤ 4 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (s + 1)]
    rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im] at h
    nlinarith
  have hs2 : (s.re - 1)^2 + s.im^2 ≤ 4 := by
    have h : Complex.normSq (s - 1) ≤ 4 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (s - 1)]
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im] at h
    nlinarith
  refine ⟨by nlinarith [sq_nonneg s.im], by nlinarith [sq_nonneg s.im],
    by nlinarith [sq_nonneg (s.re + 1)], by nlinarith [sq_nonneg (s.re + 1)], ?_⟩
  intro hc
  rcases hc with h | h | h | h
  · left
    apply Complex.ext
    · simpa using h
    · have him2 : s.im^2 ≤ 0 := by nlinarith
      have : s.im = 0 := by nlinarith
      simpa using this
  · right
    apply Complex.ext
    · simpa using h
    · have him2 : s.im^2 ≤ 0 := by nlinarith
      have : s.im = 0 := by nlinarith
      simpa using this
  · exfalso; nlinarith [sq_nonneg s.re]
  · exfalso; nlinarith [sq_nonneg s.re]

/-- **Reduction of the existence of a bounded complementary component to the normalised case
(with the two cut points available).**

Call a curve `γ : Circle → ℂ` *normalised* when its range lies in the rectangle `[-1,1] × [-2,2]`,
meets the boundary of that rectangle only in the two points `-1` and `1`, and contains both of those
points — these are the four hypotheses on `γ` in the first argument `h` below.  The claim is that to
establish, for every continuous injective `γ : Circle → ℂ`, that the complement of `range γ` has a
bounded connected component, it suffices to establish it for normalised curves.

Proof: take `p q ∈ range γ` at maximal Euclidean distance `D = ‖p - q‖ > 0` (possible since `range γ`
is compact), and put `T z = 2 (z - p)/(q - p) - 1`.  Then `T p = -1`, `T q = 1` and `T` is a
similarity (`‖T z - T w‖ = (2/D) ‖z - w‖`).  For `z ∈ range γ` the two bounds `‖z - p‖ ≤ D`,
`‖z - q‖ ≤ D` give `‖T z + 1‖ ≤ 2` and `‖T z - 1‖ ≤ 2`, which force `|(T z).re| ≤ 1` and
`|(T z).im| ≤ 2` (lens computation), and force `T z = ±1` as soon as one of the coordinates is
`±1` or `±2`; moreover `T p = -1` and `T q = 1` lie in `range (T ∘ γ)`.  Finally `T` is a
homeomorphism Lipschitz in both directions, so the conclusion transfers from `T ∘ γ` back to `γ`. -/
theorem normalized_reduction_bounded_component
    (h : ∀ (γ : Circle → ℂ), Continuous γ → Function.Injective γ →
        (∀ z ∈ Set.range γ, -1 ≤ z.re ∧ z.re ≤ 1 ∧ -2 ≤ z.im ∧ z.im ≤ 2) →
        (∀ z ∈ Set.range γ, (z.re = -1 ∨ z.re = 1 ∨ z.im = -2 ∨ z.im = 2) →
          z = -1 ∨ z = 1) →
        (-1 : ℂ) ∈ Set.range γ → (1 : ℂ) ∈ Set.range γ →
        ∃ x : ℂ, x ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x))
    (γ : Circle → ℂ) (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ x : ℂ, x ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x) := by
  -- a pair of points of `range γ` at maximal distance, and the associated similarity
  obtain ⟨p, hp, q, hq, hpq, hmax⟩ := exists_max_dist_pair γ hγ hinj
  have hqp : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  set c : ℂ := 2 / (q - p) with hc_def
  have hc : c ≠ 0 := by rw [hc_def]; exact div_ne_zero two_ne_zero hqp
  set b : ℂ := -(2 * p / (q - p)) - 1 with hb_def
  let T : ℂ → ℂ := fun z => c * z + b
  let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addRight b)
  have he_coe : ⇑e = T := by
    funext z
    show ((Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addRight b)) z = T z
    rw [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
  have he_symm : ⇑e.symm = fun z => c⁻¹ * (z - b) := by
    funext z
    rw [Homeomorph.symm_apply_eq]
    show z = ((Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addRight b)) (c⁻¹ * (z - b))
    rw [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
    show z = c * (c⁻¹ * (z - b)) + b
    field_simp
    ring
  -- `T` is exactly the map `z ↦ 2 (z - p)/(q - p) - 1` of the docstring
  have hT_eq : ∀ z : ℂ, T z = 2 * (z - p) / (q - p) - 1 := by
    intro z
    show c * z + b = 2 * (z - p) / (q - p) - 1
    rw [hc_def, hb_def]
    field_simp
    ring
  have hTadd : ∀ z : ℂ, T z + 1 = 2 * (z - p) / (q - p) := by
    intro z; rw [hT_eq z]; ring
  have hTsub : ∀ z : ℂ, T z - 1 = 2 * (z - q) / (q - p) := by
    intro z; rw [hT_eq z]; field_simp; ring
  have hDpos : 0 < ‖q - p‖ := norm_pos_iff.mpr hqp
  -- the two distance bounds provided by maximality
  have hzp_le : ∀ z ∈ Set.range γ, ‖z - p‖ ≤ ‖q - p‖ := by
    intro z hz
    have h := hmax z hz p hp
    rwa [norm_sub_rev p q] at h
  have hzq_le : ∀ z ∈ Set.range γ, ‖z - q‖ ≤ ‖q - p‖ := by
    intro z hz
    have h := hmax z hz q hq
    rwa [norm_sub_rev p q] at h
  -- `T` maps `range γ` into the lens of the two discs
  have hbound1 : ∀ z ∈ Set.range γ, ‖T z + 1‖ ≤ 2 := by
    intro z hz
    calc ‖T z + 1‖ = 2 * ‖z - p‖ / ‖q - p‖ := by
          rw [hTadd z, norm_div, norm_mul]; norm_num
      _ ≤ 2 := by rw [div_le_iff₀ hDpos]; linarith [hzp_le z hz]
  have hbound2 : ∀ z ∈ Set.range γ, ‖T z - 1‖ ≤ 2 := by
    intro z hz
    calc ‖T z - 1‖ = 2 * ‖z - q‖ / ‖q - p‖ := by
          rw [hTsub z, norm_div, norm_mul]; norm_num
      _ ≤ 2 := by rw [div_le_iff₀ hDpos]; linarith [hzq_le z hz]
  -- the normalised curve `T ∘ γ`
  have hmemb : ∀ z ∈ Set.range (fun c : Circle => T (γ c)),
      -1 ≤ z.re ∧ z.re ≤ 1 ∧ -2 ≤ z.im ∧ z.im ≤ 2 := by
    rintro z ⟨c0, rfl⟩
    obtain ⟨a1, a2, a3, a4, -⟩ :=
      lens_mem_rect_of_norm_le_two (T (γ c0)) (hbound1 _ ⟨c0, rfl⟩) (hbound2 _ ⟨c0, rfl⟩)
    exact ⟨a1, a2, a3, a4⟩
  have hbd : ∀ z ∈ Set.range (fun c : Circle => T (γ c)),
      (z.re = -1 ∨ z.re = 1 ∨ z.im = -2 ∨ z.im = 2) → z = -1 ∨ z = 1 := by
    rintro z ⟨c0, rfl⟩ hz
    exact (lens_mem_rect_of_norm_le_two (T (γ c0)) (hbound1 _ ⟨c0, rfl⟩)
      (hbound2 _ ⟨c0, rfl⟩)).2.2.2.2 hz
  have hminus : (-1 : ℂ) ∈ Set.range (fun c : Circle => T (γ c)) := by
    obtain ⟨c0, hc0⟩ := hp
    refine ⟨c0, ?_⟩
    show T (γ c0) = -1
    rw [hc0, hT_eq]
    simp
  have hplus : (1 : ℂ) ∈ Set.range (fun c : Circle => T (γ c)) := by
    obtain ⟨c0, hc0⟩ := hq
    refine ⟨c0, ?_⟩
    show T (γ c0) = 1
    rw [hc0, hT_eq, mul_div_cancel_right₀ 2 hqp]
    norm_num
  have hTinj : Function.Injective T := by
    intro z w hzw
    rw [hT_eq z, hT_eq w] at hzw
    have h1 : 2 * (z - p) / (q - p) = 2 * (w - p) / (q - p) := sub_left_inj.mp hzw
    have h2 : 2 * (z - p) * (q - p) = 2 * (w - p) * (q - p) :=
      (div_eq_div_iff hqp hqp).mp h1
    have h3 : 2 * (z - p) = 2 * (w - p) := mul_right_cancel₀ hqp h2
    have h4 : z - p = w - p := mul_left_cancel₀ two_ne_zero h3
    exact sub_left_inj.mp h4
  have hTinj' : Function.Injective (fun c : Circle => T (γ c)) := hTinj.comp hinj
  have hcont' : Continuous (fun c : Circle => T (γ c)) :=
    (he_coe ▸ e.continuous).comp hγ
  -- the induction hypothesis for the normalised curve
  obtain ⟨x, hx, hb⟩ := h (fun c : Circle => T (γ c)) hcont' hTinj' hmemb hbd hminus hplus
  -- transport back along the inverse of the similarity
  have hfun : (fun c : Circle => e (γ c)) = fun c => T (γ c) := by
    funext c; rw [he_coe]
  have hbdd : ∀ S : Set ℂ, Bornology.IsBounded S → Bornology.IsBounded (e.symm '' S) := by
    intro S hS
    simpa only [he_symm] using (isBounded_image_affine (c := c) (b := b) hc hS).2
  have hx' : x ∉ Set.range (fun c : Circle => e (γ c)) := by rw [hfun]; exact hx
  have hb' : Bornology.IsBounded
      (connectedComponentIn ((Set.range (fun c : Circle => e (γ c)))ᶜ) x) := by
    rw [hfun]; exact hb
  obtain ⟨y, hy, hyb⟩ := exists_bounded_component_of_homeomorph e hbdd γ x hx' hb'
  exact ⟨y, hy, hyb⟩

end Work.RPB1a.Caratheodory.Brouwer
