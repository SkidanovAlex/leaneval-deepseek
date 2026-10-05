import Mathlib
import Submission.Work.RPB.B1a.jordan_separation_plane
import Submission.Work.RPB1a.Caratheodory.chordImage_isJordanCurveSet
import Submission.Work.RPB1a.Caratheodory.frontier_sphere_image
import Submission.Work.RPB1a.Caratheodory.isPreconnected_frontier_diff_singleton

namespace Work.RPB.B1a

open Complex Set Metric
open scoped Topology Convex

/-!
# `Work.RPB.B1a.exists_arc_const_of_eqOn_sphere`

Topological half of Carathéodory's boundary correspondence (see the docstring of the theorem).

The proof uses the plane separation of the *chord* `Γ = Ψ '' segment ℝ p q` (a Jordan curve, by
`Work.RPB1a.Caratheodory.chordImage_isJordanCurveSet`, separated by
`Work.RPB.B1a.jordan_separation_plane`).  The two open half-discs cut off by the chord have images
in *different* sides of `Γ`, which forces the frontier of `D` (a circle minus `y = Ψ p = Ψ q`) to be
split into the two image arcs, one of which must be the single point `{y}`.
-/

section Geometry

variable (p q : ℂ)

/-- The signed position of `z` with respect to the chord joining `p` and `q`: the imaginary part of
`(z - p)/(q - p)`.  It vanishes exactly on the line through `p` and `q`. -/
noncomputable def cS (z : ℂ) : ℝ := ((z - p) / (q - p)).im

lemma cS_apply (z : ℂ) : cS p q z = ((z - p) / (q - p)).im := rfl

@[simp] lemma cS_left : cS p q p = 0 := by simp [cS]

lemma cS_right (hpq : p ≠ q) : cS p q q = 0 := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  simp only [cS]
  rw [div_self hd]
  simp

/-- `cS` is affine over `ℝ`. -/
lemma cS_affine {a b : ℝ} (hab : a + b = 1) (x y : ℂ) :
    cS p q (a • x + b • y) = a * cS p q x + b * cS p q y := by
  have hab' : (a : ℂ) + (b : ℂ) = 1 := by
    rw [← Complex.ofReal_add, hab, Complex.ofReal_one]
  have h1 : a • x + b • y - p = a • (x - p) + b • (y - p) := by
    simp only [real_smul]
    rw [show (a : ℂ) * (x - p) + (b : ℂ) * (y - p)
        = (a : ℂ) * x + (b : ℂ) * y - ((a : ℂ) + (b : ℂ)) * p by ring, hab', one_mul]
  have h2 : (a • x + b • y - p) / (q - p)
      = a • ((x - p) / (q - p)) + b • ((y - p) / (q - p)) := by
    rw [h1]
    simp only [real_smul]
    rw [add_div, mul_div_assoc, mul_div_assoc]
  rw [cS_apply, h2]
  simp only [real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, cS_apply]

/-- The half-plane `cS > 0` is convex. -/
lemma convex_cS_pos : Convex ℝ {z : ℂ | 0 < cS p q z} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [cS_affine p q hab]
  positivity

/-- The half-plane `cS < 0` is convex. -/
lemma convex_cS_neg : Convex ℝ {z : ℂ | cS p q z < 0} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  rw [cS_affine p q hab]
  nlinarith

/-- `cS` vanishes on every point of the chord. -/
lemma cS_chord (hpq : p ≠ q) (t : ℝ) : cS p q ((1 - t) • p + t • q) = 0 := by
  rw [cS_affine p q (by ring : (1 - t) + t = 1), cS_left, cS_right p q hpq]
  ring

/-- A point of the chord-line is an affine combination of `p` and `q`. -/
lemma cS_eq_zero_line {hpq : p ≠ q} {z : ℂ} (h : cS p q z = 0) :
    ∃ t : ℝ, z = (1 - t) • p + t • q := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have him : ((z - p) / (q - p)).im = 0 := by rw [← cS_apply]; exact h
  have hz : (z - p) / (q - p) = (((z - p) / (q - p)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  set t0 : ℝ := ((z - p) / (q - p)).re with ht0
  have h2 : z - p = t0 • (q - p) := by
    have h5 : (t0 : ℂ) * (q - p) = z - p := by
      rw [ht0, ← hz]; exact div_mul_cancel₀ (z - p) hd
    rw [real_smul]; exact h5.symm
  have h3 : z = p + t0 • (q - p) := by
    rw [← h2]; ring
  refine ⟨t0, ?_⟩
  rw [h3, smul_sub, sub_smul, one_smul]
  abel

end Geometry

section NormFormula

variable {p q : ℂ}

/-- The complex conjugate of a point of the unit circle again has norm `1`. -/
lemma norm_conj_eq_one {q : ℂ} (hq : ‖q‖ = 1) : ‖(starRingEnd ℂ) q‖ = 1 := by
  have h : Complex.normSq ((starRingEnd ℂ) q) = Complex.normSq q := Complex.normSq_conj q
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hq] at h
  nlinarith [norm_nonneg ((starRingEnd ℂ) q)]

/-- The real part of `p * conj q` is `< 1` for two distinct points of the unit circle. -/
lemma chord_re_lt_one (hpq : p ≠ q) (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) : (p * (starRingEnd ℂ) q).re < 1 := by
  have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hqn : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hstarn : ‖(starRingEnd ℂ) q‖ = 1 := norm_conj_eq_one hqn
  have hle : (p * (starRingEnd ℂ) q).re ≤ 1 := by
    calc (p * (starRingEnd ℂ) q).re ≤ ‖p * (starRingEnd ℂ) q‖ := Complex.re_le_norm _
      _ = ‖p‖ * ‖(starRingEnd ℂ) q‖ := norm_mul _ _
      _ = 1 := by rw [hpn, hstarn, one_mul]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hn1 : ‖p * (starRingEnd ℂ) q‖ = 1 := by rw [norm_mul, hpn, hstarn, one_mul]
    have him : (p * (starRingEnd ℂ) q).im = 0 := by
      have h2 : ‖p * (starRingEnd ℂ) q‖ ^ 2 = (p * (starRingEnd ℂ) q).re ^ 2
          + (p * (starRingEnd ℂ) q).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hn1, h] at h2
      nlinarith [sq_nonneg (p * (starRingEnd ℂ) q).im]
    have hpqq : p * (starRingEnd ℂ) q = 1 := by
      apply Complex.ext
      · simpa using h
      · simpa using him
    have hpq' : p = q := by
      have h2 : (starRingEnd ℂ) q * q = 1 := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hqn]; norm_num
      have h4 := congrArg (fun w => w * q) hpqq
      simp only [one_mul] at h4
      rw [mul_assoc, h2, mul_one] at h4
      exact h4
    exact hpq hpq'

/-- The squared norm of a point of the chord, in terms of the parameter. -/
lemma chord_normSq (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (t : ℝ) :
    Complex.normSq ((1 - t) • p + t • q)
      = 1 - 2 * (t * (1 - t)) * (1 - (p * (starRingEnd ℂ) q).re) := by
  have hp' : Complex.normSq p = 1 := by rw [Complex.normSq_eq_norm_sq, hp]; norm_num
  have hq' : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq, hq]; norm_num
  have hrw : (1 - t) • p + t • q = ((1 - t : ℝ) : ℂ) * p + ((t : ℝ) : ℂ) * q := by
    simp [real_smul]
  rw [hrw, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal, hp', hq']
  rw [show (starRingEnd ℂ) (((t : ℝ) : ℂ) * q) = ((t : ℝ) : ℂ) * (starRingEnd ℂ) q by
    rw [map_mul, Complex.conj_ofReal]]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

/-- A chord point on the unit circle is an endpoint. -/
lemma chord_mem_sphere {hpq : p ≠ q} (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) {t : ℝ}
    (h : ‖(1 - t) • p + t • q‖ = 1) : t = 0 ∨ t = 1 := by
  have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hqn : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hc : (p * (starRingEnd ℂ) q).re < 1 := chord_re_lt_one hpq hp hq
  have hnsq' : 1 - 2 * (t * (1 - t)) * (1 - (p * (starRingEnd ℂ) q).re) = 1 := by
    rw [← chord_normSq hpn hqn t, Complex.normSq_eq_norm_sq, h]
    norm_num
  have h2 : 2 * (t * (1 - t)) * (1 - (p * (starRingEnd ℂ) q).re) = 0 := by linarith
  have h3 : (1 - (p * (starRingEnd ℂ) q).re) ≠ 0 := by linarith
  have h4 : 2 * (t * (1 - t)) = 0 := (mul_eq_zero.mp h2).resolve_right h3
  have ht : t * (1 - t) = 0 := (mul_eq_zero.mp h4).resolve_left (by norm_num)
  rcases mul_eq_zero.mp ht with h' | h'
  · left; linarith
  · right; linarith

/-- A chord point in the open disc is an interior point of the chord. -/
lemma chord_mem_ball {hpq : p ≠ q} (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) {t : ℝ}
    (h : ‖(1 - t) • p + t • q‖ < 1) : 0 < t ∧ t < 1 := by
  have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hqn : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hc : (p * (starRingEnd ℂ) q).re < 1 := chord_re_lt_one hpq hp hq
  have hnsq := chord_normSq hpn hqn t
  have h1 : ‖(1 - t) • p + t • q‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg ((1 - t) • p + t • q)]
  rw [← Complex.normSq_eq_norm_sq, hnsq] at h1
  have h2 : 0 < t * (1 - t) := by nlinarith
  constructor <;> nlinarith [h2]

end NormFormula

section TwoSigns

variable {p q : ℂ}

/-- On the unit circle, `cS` takes values of both signs. -/
lemma exists_cS_pos_and_neg (hpq : p ≠ q) (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) :
    (∃ z ∈ Metric.sphere 0 1, 0 < cS p q z) ∧ (∃ z ∈ Metric.sphere 0 1, cS p q z < 0) := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hVne : Complex.I * (q - p) ≠ 0 := mul_ne_zero Complex.I_ne_zero hd
  set m : ℂ := (1/2 : ℝ) • p + (1/2 : ℝ) • q with hm
  set V : ℂ := Complex.I * (q - p) with hV
  have hVne' : V ≠ 0 := by rw [hV]; exact hVne
  have hVnorm' : 0 < ‖V‖ := norm_pos_iff.mpr hVne'
  have hmcs : cS p q m = 0 := by
    rw [hm, cS_affine p q (by norm_num : (1/2:ℝ) + 1/2 = 1), cS_left, cS_right p q hpq]
    ring
  have hmn : ‖m‖ < 1 := by
    have hbc : m ∈ Metric.ball (0:ℂ) 1 := by
      have hsc := (strictConvex_closedBall ℝ (0:ℂ) 1).openSegment_subset
        (Metric.sphere_subset_closedBall hp) (Metric.sphere_subset_closedBall hq) hpq
      rw [interior_closedBall (0:ℂ) one_ne_zero] at hsc
      exact hsc ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, hm.symm⟩
    rwa [Metric.mem_ball, dist_zero_right] at hbc
  have hVplus : cS p q (m + V) = 1 := by
    rw [cS_apply]
    have hmp : (m - p) / (q - p) = (1/2 : ℂ) := by
      have hm1 : m - p = (1/2:ℝ) • (q - p) := by rw [hm]; module
      rw [hm1, real_smul, mul_div_assoc, div_self hd, mul_one]
      norm_num
    have hVq : V / (q - p) = Complex.I := by
      rw [hV, mul_div_assoc, div_self hd, mul_one]
    have hsplit : (m + V - p) / (q - p) = (m - p)/(q - p) + V/(q - p) := by
      rw [show m + V - p = (m - p) + V by ring, add_div]
    rw [hsplit, hmp, hVq]
    simp [Complex.I_im]
  have hVminus : cS p q (m - V) = -1 := by
    have hmid : m = (1/2:ℝ) • (m + V) + (1/2:ℝ) • (m - V) := by
      module
    have h := cS_affine p q (show (1/2:ℝ) + 1/2 = 1 by norm_num) (m + V) (m - V)
    rw [← hmid, hmcs, hVplus] at h
    linarith
  have key : ∀ (r : ℝ) (w : ℂ), cS p q (m + r • w) = r * cS p q (m + w) := by
    intro r w
    have hmid : m + r • w = (1 - r) • m + r • (m + w) := by
      simp only [smul_add]; module
    rw [hmid, cS_affine p q (by ring : (1 - r) + r = 1), hmcs]
    ring
  have hIVT : ∀ w : ℂ, w ≠ 0 → ∃ r : ℝ, 0 < r ∧ ‖m + r • w‖ = 1 := by
    intro w hw
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set S : ℝ := (2 + ‖m‖) / ‖w‖ with hSdef
    have hSpos : 0 < S := by rw [hSdef]; positivity
    have hSbig : 1 < ‖m + S • w‖ := by
      have h1 : ‖S • w‖ = 2 + ‖m‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hSpos.le, hSdef,
          div_mul_cancel₀ (2 + ‖m‖) (ne_of_gt hwn)]
      have h2 := norm_sub_le (m + S • w) m
      rw [add_sub_cancel_left, h1] at h2
      linarith
    have hcont : ContinuousOn (fun r : ℝ => ‖m + r • w‖) (Set.Icc (0:ℝ) S) := by fun_prop
    have h1 : (1:ℝ) ∈ Set.Icc (‖m + (0:ℝ) • w‖) (‖m + S • w‖) := by
      rw [zero_smul, add_zero]
      exact ⟨le_of_lt hmn, le_of_lt hSbig⟩
    obtain ⟨r, hr, hrw⟩ :=
      (intermediate_value_Icc (a := (0:ℝ)) (b := S) hSpos.le hcont h1)
    change ‖m + r • w‖ = 1 at hrw
    refine ⟨r, ?_, hrw⟩
    rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h, zero_smul, add_zero] at hrw
      exact absurd hrw (by linarith [hmn])
    · exact h
  obtain ⟨s, hspos, hs⟩ := hIVT V hVne'
  obtain ⟨s', hs'pos, hs'⟩ := hIVT (-V) (neg_ne_zero.mpr hVne')
  exact ⟨⟨m + s • V, by rw [mem_sphere_zero_iff_norm]; exact hs, by rw [key s V, hVplus]; linarith⟩,
    ⟨m + s' • (-V), by rw [mem_sphere_zero_iff_norm]; exact hs',
      by rw [key s' (-V), show m + (-V) = m - V by ring, hVminus]; linarith⟩⟩

end TwoSigns

section Continuity

variable (p q : ℂ)

lemma continuous_cS : Continuous (cS p q) := by
  change Continuous (fun z : ℂ => ((z - p) / (q - p)).im)
  exact Complex.continuous_im.comp ((continuous_id.sub continuous_const).div_const _)

end Continuity

section ChordSet

variable {p q : ℂ}

/-- The chord is contained in the closed unit disc. -/
lemma segment_subset_closedBall (hp : p ∈ Metric.sphere 0 1) (hq : q ∈ Metric.sphere 0 1) :
    segment ℝ p q ⊆ Metric.closedBall (0 : ℂ) 1 :=
  (convex_closedBall (0 : ℂ) 1).segment_subset (Metric.sphere_subset_closedBall hp)
    (Metric.sphere_subset_closedBall hq)

/-- The open chord is contained in the open unit disc. -/
lemma openSegment_subset_ball {hpq : p ≠ q} (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) : openSegment ℝ p q ⊆ Metric.ball (0 : ℂ) 1 := by
  have hsc := (strictConvex_closedBall ℝ (0 : ℂ) 1).openSegment_subset
    (Metric.sphere_subset_closedBall hp) (Metric.sphere_subset_closedBall hq) hpq
  rwa [interior_closedBall (0 : ℂ) one_ne_zero] at hsc

/-- The points of the chord lying in the open disc are exactly the interior points of the chord. -/
lemma segment_inter_ball {hpq : p ≠ q} (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) {w : ℂ} (hw : w ∈ segment ℝ p q)
    (hwb : w ∈ Metric.ball (0 : ℂ) 1) : w ∈ openSegment ℝ p q := by
  obtain ⟨a, b, ha, hb, hab, hwab⟩ := hw
  have haeq : a = 1 - b := by linarith
  have hwb' : w = (1 - b) • p + b • q := by rw [← hwab, haeq]
  have hlt : ‖(1 - b) • p + b • q‖ < 1 := by
    have := hwb
    rw [Metric.mem_ball, dist_zero_right] at this
    rwa [← hwb']
  obtain ⟨h0, h1⟩ := chord_mem_ball (hpq := hpq) hp hq hlt
  exact ⟨a, b, by linarith, h0, hab, hwab⟩

/-- The points of the chord lying on the unit circle are the endpoints. -/
lemma segment_inter_sphere {hpq : p ≠ q} (hp : p ∈ Metric.sphere 0 1)
    (hq : q ∈ Metric.sphere 0 1) {w : ℂ} (hw : w ∈ segment ℝ p q)
    (hws : w ∈ Metric.sphere (0 : ℂ) 1) : w = p ∨ w = q := by
  obtain ⟨a, b, ha, hb, hab, hwab⟩ := hw
  have haeq : a = 1 - b := by linarith
  have hwb' : w = (1 - b) • p + b • q := by rw [← hwab, haeq]
  have heq : ‖(1 - b) • p + b • q‖ = 1 := by
    have := hws
    rw [mem_sphere_zero_iff_norm] at this
    rwa [← hwb']
  rcases chord_mem_sphere (hpq := hpq) hp hq heq with h0 | h1
  · left; rw [hwb', h0]; simp
  · right; rw [hwb', h1]; simp

end ChordSet

theorem exists_arc_const_of_eqOn_sphere {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (hJ : Nonempty (frontier D ≃ₜ Circle))
    {Ψ : ℂ → ℂ} (hΨc : ContinuousOn Ψ (Metric.closedBall 0 1)) (hΨi : Set.InjOn Ψ (Metric.ball 0 1))
    (hΨs : Ψ '' Metric.ball 0 1 = D) (hmt : Set.MapsTo Ψ (Metric.sphere 0 1) (frontier D))
    {p q : ℂ} (hp : p ∈ Metric.sphere 0 1) (hq : q ∈ Metric.sphere 0 1) (hpq : p ≠ q)
    (h : Ψ p = Ψ q) :
    ∃ u ∈ Metric.sphere 0 1, ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ Metric.sphere 0 1, ‖z - u‖ < δ → Ψ z = Ψ p := by
  classical
  set y : ℂ := Ψ p with hy
  have hyq : Ψ q = y := by rw [hy]; exact h.symm
  have hfront : Ψ '' Metric.sphere 0 1 = frontier D :=
    Work.RPB1a.Caratheodory.image_sphere_eq_frontier hDo hΨc hΨs hmt
  have hyfront : y ∈ frontier D := by rw [hy]; exact hmt hp
  set Γ : Set ℂ := Ψ '' segment ℝ p q with hΓdef
  have hΓ : Nonempty (Γ ≃ₜ Circle) :=
    Work.RPB1a.Caratheodory.chordImage_isJordanCurveSet hp hq hpq hΨc hΨi h
  have hyΓ : y ∈ Γ := ⟨p, ⟨1, 0, by norm_num, by norm_num, by norm_num, by simp⟩, hy.symm⟩
  set Wp : Set ℂ := Metric.ball 0 1 ∩ {z | 0 < cS p q z} with hWp
  set Wm : Set ℂ := Metric.ball 0 1 ∩ {z | cS p q z < 0} with hWm
  set Ap : Set ℂ := Metric.sphere 0 1 ∩ {z | 0 < cS p q z} with hAp
  set Am : Set ℂ := Metric.sphere 0 1 ∩ {z | cS p q z < 0} with hAm
  set Bp : Set ℂ := Metric.sphere 0 1 ∩ {z | 0 ≤ cS p q z} with hBp
  set Bm : Set ℂ := Metric.sphere 0 1 ∩ {z | cS p q z ≤ 0} with hBm
  have hWpball : Wp ⊆ Metric.ball (0:ℂ) 1 := fun z hz => (by rw [hWp] at hz; exact hz.1)
  have hWmball : Wm ⊆ Metric.ball (0:ℂ) 1 := fun z hz => (by rw [hWm] at hz; exact hz.1)
  have hWpcs : ∀ z ∈ Wp, 0 < cS p q z := fun z hz => (by rw [hWp] at hz; exact hz.2)
  have hWmcs : ∀ z ∈ Wm, cS p q z < 0 := fun z hz => (by rw [hWm] at hz; exact hz.2)
  have hoscs : ∀ z ∈ openSegment ℝ p q, cS p q z = 0 := by
    rintro z ⟨a, b, ha, hb, hab, hzab⟩
    have : a = 1 - b := by linarith
    rw [← hzab, this]
    exact cS_chord p q hpq b
  -- ## the images of the two half-discs avoid the chord curve
  have hWpΓ : Ψ '' Wp ⊆ Γᶜ := by
    rintro z ⟨w, hw, rfl⟩ hmem
    rw [hΓdef, Set.mem_image] at hmem
    obtain ⟨w', hw's, hw'e⟩ := hmem
    have hwb : w ∈ Metric.ball (0:ℂ) 1 := hWpball hw
    have hwcs : 0 < cS p q w := hWpcs w hw
    have hw'cb : w' ∈ Metric.closedBall (0:ℂ) 1 := segment_subset_closedBall hp hq hw's
    have hwo : Ψ w' = Ψ w := hw'e
    have hw'case : w' ∈ Metric.ball (0:ℂ) 1 ∨ w' ∈ Metric.sphere (0:ℂ) 1 := by
      have := hw'cb; rwa [← Metric.ball_union_sphere] at this
    rcases hw'case with hwb' | hws'
    · have hw'os : w' ∈ openSegment ℝ p q := segment_inter_ball (hpq := hpq) hp hq hw's hwb'
      have hweq : w = w' := hΨi hwb hwb' hwo.symm
      have h0 : cS p q w = 0 := by rw [hweq]; exact hoscs w' hw'os
      linarith
    · have hwp' : w' = p ∨ w' = q := segment_inter_sphere (hpq := hpq) hp hq hw's hws'
      have hwy : Ψ w = y := by
        rcases hwp' with hh | hh
        · rw [hh] at hwo; exact hwo.symm.trans hy.symm
        · rw [hh] at hwo; exact hwo.symm.trans hyq
      have hwD : Ψ w ∈ D := by rw [← hΨs]; exact ⟨w, hwb, rfl⟩
      have hwf : Ψ w ∈ frontier D := by rw [hwy]; exact hyfront
      rw [IsOpen.frontier_eq hDo] at hwf
      exact hwf.2 hwD
  have hWmΓ : Ψ '' Wm ⊆ Γᶜ := by
    rintro z ⟨w, hw, rfl⟩ hmem
    rw [hΓdef, Set.mem_image] at hmem
    obtain ⟨w', hw's, hw'e⟩ := hmem
    have hwb : w ∈ Metric.ball (0:ℂ) 1 := hWmball hw
    have hwcs : cS p q w < 0 := hWmcs w hw
    have hw'cb : w' ∈ Metric.closedBall (0:ℂ) 1 := segment_subset_closedBall hp hq hw's
    have hwo : Ψ w' = Ψ w := hw'e
    have hw'case : w' ∈ Metric.ball (0:ℂ) 1 ∨ w' ∈ Metric.sphere (0:ℂ) 1 := by
      have := hw'cb; rwa [← Metric.ball_union_sphere] at this
    rcases hw'case with hwb' | hws'
    · have hw'os : w' ∈ openSegment ℝ p q := segment_inter_ball (hpq := hpq) hp hq hw's hwb'
      have hweq : w = w' := hΨi hwb hwb' hwo.symm
      have h0 : cS p q w = 0 := by rw [hweq]; exact hoscs w' hw'os
      linarith
    · have hwp' : w' = p ∨ w' = q := segment_inter_sphere (hpq := hpq) hp hq hw's hws'
      have hwy : Ψ w = y := by
        rcases hwp' with hh | hh
        · rw [hh] at hwo; exact hwo.symm.trans hy.symm
        · rw [hh] at hwo; exact hwo.symm.trans hyq
      have hwD : Ψ w ∈ D := by rw [← hΨs]; exact ⟨w, hwb, rfl⟩
      have hwf : Ψ w ∈ frontier D := by rw [hwy]; exact hyfront
      rw [IsOpen.frontier_eq hDo] at hwf
      exact hwf.2 hwD
  -- ## Jordan separation of the chord curve
  obtain ⟨ins, out, hio, hoo, hic, hoc, hib, hob, hcov, hdisj, hfi, hfo⟩ :=
    jordan_separation_plane Γ hΓ
  have houtc : out ⊆ Γᶜ := by rw [hcov]; exact Set.subset_union_right
  have hinc : ins ⊆ Γᶜ := by rw [hcov]; exact Set.subset_union_left
  have hWp_pre : IsPreconnected Wp := by
    rw [hWp]; exact (convex_ball (0:ℂ) 1).inter (convex_cS_pos p q) |>.isPreconnected
  have hWm_pre : IsPreconnected Wm := by
    rw [hWm]; exact (convex_ball (0:ℂ) 1).inter (convex_cS_neg p q) |>.isPreconnected
  have hWp_cov : Ψ '' Wp ⊆ ins ∪ out := by rw [← hcov]; exact hWpΓ
  have hWm_cov : Ψ '' Wm ⊆ ins ∪ out := by rw [← hcov]; exact hWmΓ
  have hWp_img : IsPreconnected (Ψ '' Wp) :=
    hWp_pre.image Ψ (hΨc.mono (fun z hz => Metric.ball_subset_closedBall (hWpball hz)))
  have hWm_img : IsPreconnected (Ψ '' Wm) :=
    hWm_pre.image Ψ (hΨc.mono (fun z hz => Metric.ball_subset_closedBall (hWmball hz)))
  have hWp_or : Ψ '' Wp ⊆ ins ∨ Ψ '' Wp ⊆ out :=
    hWp_img.subset_or_subset hio hoo hdisj hWp_cov
  have hWm_or : Ψ '' Wm ⊆ ins ∨ Ψ '' Wm ⊆ out :=
    hWm_img.subset_or_subset hio hoo hdisj hWm_cov
  -- ## `D \ Γ` is the union of the two half-disc images
  have hDΓ : D \ Γ = Ψ '' Wp ∪ Ψ '' Wm := by
    ext z; constructor
    · intro hz
      obtain ⟨hzD, hzG⟩ := hz
      rw [← hΨs, Set.mem_image] at hzD
      obtain ⟨w, hwb, hwz⟩ := hzD
      have hwcs : cS p q w ≠ 0 := by
        intro h0
        obtain ⟨t, ht⟩ := cS_eq_zero_line p q (hpq := hpq) h0
        have hlt : ‖(1-t)•p + t•q‖ < 1 := by
          have h1 := hwb; rw [Metric.mem_ball, dist_zero_right] at h1
          rwa [← ht]
        obtain ⟨ht0, ht1⟩ := chord_mem_ball (hpq := hpq) hp hq hlt
        exact hzG ⟨w, openSegment_subset_segment ℝ p q
          ⟨1-t, t, by linarith, ht0, by ring, ht.symm⟩, hwz⟩
      rcases lt_or_gt_of_ne hwcs with hlt | hlt
      · right; exact ⟨w, by rw [hWm]; exact ⟨hwb, hlt⟩, hwz⟩
      · left; exact ⟨w, by rw [hWp]; exact ⟨hwb, hlt⟩, hwz⟩
    · rintro (hz | hz)
      · obtain ⟨w, hw, hwz⟩ := hz
        refine ⟨?_, ?_⟩
        · rw [← hwz, ← hΨs]; exact ⟨w, hWpball hw, rfl⟩
        · rw [← hwz]; exact hWpΓ ⟨w, hw, rfl⟩
      · obtain ⟨w, hw, hwz⟩ := hz
        refine ⟨?_, ?_⟩
        · rw [← hwz, ← hΨs]; exact ⟨w, hWmball hw, rfl⟩
        · rw [← hwz]; exact hWmΓ ⟨w, hw, rfl⟩
  -- ## the middle point of the chord
  have hm0ball : (1/2:ℝ) • p + (1/2:ℝ) • q ∈ Metric.ball (0:ℂ) 1 := by
    have hsc := (strictConvex_closedBall ℝ (0:ℂ) 1).openSegment_subset
      (Metric.sphere_subset_closedBall hp) (Metric.sphere_subset_closedBall hq) hpq
    rw [interior_closedBall (0:ℂ) one_ne_zero] at hsc
    exact hsc ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hm0D : Ψ ((1/2:ℝ) • p + (1/2:ℝ) • q) ∈ D := by
    rw [← hΨs]; exact ⟨_, hm0ball, rfl⟩
  have hm0G : Ψ ((1/2:ℝ) • p + (1/2:ℝ) • q) ∈ Γ :=
    ⟨_, ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩, rfl⟩
  -- ## neither half-disc image lies in `ins`, nor both in `out`
  have hnot_in : ¬ (Ψ '' Wp ⊆ ins ∧ Ψ '' Wm ⊆ ins) := by
    rintro ⟨hpi, hmi⟩
    have hDins : D \ Γ ⊆ ins := by rw [hDΓ]; exact Set.union_subset hpi hmi
    have hDsub : D ⊆ ins ∪ Γ := by
      intro z hz
      by_cases hzG : z ∈ Γ
      · exact Or.inr hzG
      · left; exact hDins ⟨hz, hzG⟩
    have hDout : D ∩ out = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzD, hzout⟩
      rcases hDsub hzD with h | h
      · exact (Set.disjoint_left.mp hdisj h hzout)
      · exact (houtc hzout) h
    have hcl : Ψ ((1/2:ℝ) • p + (1/2:ℝ) • q) ∈ closure out :=
      frontier_subset_closure (by rw [hfo]; exact hm0G)
    obtain ⟨ε, hε, hεsub⟩ := isOpen_iff.mp hDo _ hm0D
    obtain ⟨w1, hw1out, hw1ε⟩ := Metric.mem_closure_iff.mp hcl ε hε
    exact (Set.eq_empty_iff_forall_notMem.mp hDout) w1
      ⟨hεsub (Metric.mem_ball.mpr (by rw [dist_comm]; exact hw1ε)), hw1out⟩
  have hnot_out : ¬ (Ψ '' Wp ⊆ out ∧ Ψ '' Wm ⊆ out) := by
    rintro ⟨hpo, hmo⟩
    have hDout' : D \ Γ ⊆ out := by rw [hDΓ]; exact Set.union_subset hpo hmo
    have hDsub : D ⊆ out ∪ Γ := by
      intro z hz
      by_cases hzG : z ∈ Γ
      · exact Or.inr hzG
      · left; exact hDout' ⟨hz, hzG⟩
    have hDins : D ∩ ins = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzD, hzin⟩
      rcases hDsub hzD with h | h
      · exact (Set.disjoint_left.mp hdisj hzin) h
      · exact (hinc hzin) h
    have hcl : Ψ ((1/2:ℝ) • p + (1/2:ℝ) • q) ∈ closure ins :=
      frontier_subset_closure (by rw [hfi]; exact hm0G)
    obtain ⟨ε, hε, hεsub⟩ := isOpen_iff.mp hDo _ hm0D
    obtain ⟨w1, hw1in, hw1ε⟩ := Metric.mem_closure_iff.mp hcl ε hε
    exact (Set.eq_empty_iff_forall_notMem.mp hDins) w1
      ⟨hεsub (Metric.mem_ball.mpr (by rw [dist_comm]; exact hw1ε)), hw1in⟩
  -- ## the arcs lie in the closure of the half-disc images
  have hApcl : Ap ⊆ closure Wp := by
    intro a ha
    rw [hAp] at ha
    obtain ⟨hasph, hacs⟩ := ha
    change 0 < cS p q a at hacs
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t : ℝ := min (1/2) (ε/4) with ht
    have htpos : 0 < t := lt_min (by norm_num) (by positivity)
    have hap : a ≠ p := by
      intro hh; rw [hh] at hacs; rw [cS_left p q] at hacs; exact absurd hacs (lt_irrefl 0)
    have ht1 : t ≤ 1/2 := min_le_left _ _
    refine ⟨(1-t)•a + t•p, ?_, ?_⟩
    · rw [hWp]
      refine ⟨?_, ?_⟩
      · have hsc := (strictConvex_closedBall ℝ (0:ℂ) 1).openSegment_subset
            (Metric.sphere_subset_closedBall hasph) (Metric.sphere_subset_closedBall hp) hap
        rw [interior_closedBall (0:ℂ) one_ne_zero] at hsc
        exact hsc ⟨1-t, t, by linarith, htpos, by ring, rfl⟩
      · change 0 < cS p q ((1-t)•a + t•p)
        rw [cS_affine p q (by ring : (1-t)+t=1), cS_left]; nlinarith
    · rw [dist_eq_norm, show a - ((1-t)•a + t•p) = t•(a-p) by module, norm_smul,
        Real.norm_eq_abs, abs_of_pos htpos]
      have hpa : ‖a - p‖ ≤ 2 := by
        calc ‖a - p‖ ≤ ‖a‖ + ‖p‖ := norm_sub_le _ _
          _ = 2 := by rw [mem_sphere_zero_iff_norm.mp hasph, mem_sphere_zero_iff_norm.mp hp]; norm_num
      have htle : t ≤ ε/4 := min_le_right _ _
      nlinarith [htpos, hε]
  have hAmcl : Am ⊆ closure Wm := by
    intro a ha
    rw [hAm] at ha
    obtain ⟨hasph, hacs⟩ := ha
    change cS p q a < 0 at hacs
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t : ℝ := min (1/2) (ε/4) with ht
    have htpos : 0 < t := lt_min (by norm_num) (by positivity)
    have haq : a ≠ q := by
      intro hh; rw [hh] at hacs; rw [cS_right p q hpq] at hacs; exact absurd hacs (lt_irrefl 0)
    have ht1 : t ≤ 1/2 := min_le_left _ _
    refine ⟨(1-t)•a + t•q, ?_, ?_⟩
    · rw [hWm]
      refine ⟨?_, ?_⟩
      · have hsc := (strictConvex_closedBall ℝ (0:ℂ) 1).openSegment_subset
            (Metric.sphere_subset_closedBall hasph) (Metric.sphere_subset_closedBall hq) haq
        rw [interior_closedBall (0:ℂ) one_ne_zero] at hsc
        exact hsc ⟨1-t, t, by linarith, htpos, by ring, rfl⟩
      · change cS p q ((1-t)•a + t•q) < 0
        rw [cS_affine p q (by ring : (1-t)+t=1), cS_right p q hpq]; nlinarith
    · rw [dist_eq_norm, show a - ((1-t)•a + t•q) = t•(a-q) by module, norm_smul,
        Real.norm_eq_abs, abs_of_pos htpos]
      have hpa : ‖a - q‖ ≤ 2 := by
        calc ‖a - q‖ ≤ ‖a‖ + ‖q‖ := norm_sub_le _ _
          _ = 2 := by rw [mem_sphere_zero_iff_norm.mp hasph, mem_sphere_zero_iff_norm.mp hq]; norm_num
      have htle : t ≤ ε/4 := min_le_right _ _
      nlinarith [htpos, hε]
  have hclWp : closure Wp ⊆ Metric.closedBall (0:ℂ) 1 :=
    closure_minimal (fun z hz => Metric.ball_subset_closedBall (hWpball hz)) isClosed_closedBall
  have hclWm : closure Wm ⊆ Metric.closedBall (0:ℂ) 1 :=
    closure_minimal (fun z hz => Metric.ball_subset_closedBall (hWmball hz)) isClosed_closedBall
  -- ## the sphere cut by the chord line
  have hszero : Metric.sphere (0:ℂ) 1 ∩ {z | cS p q z = 0} = {p, q} := by
    ext z; constructor
    · rintro ⟨hzs, hz0⟩
      obtain ⟨t, ht⟩ := cS_eq_zero_line p q (hpq := hpq) hz0
      have heq : ‖(1-t)•p + t•q‖ = 1 := by
        have h1 := hzs; rw [mem_sphere_zero_iff_norm] at h1
        rwa [← ht]
      rcases chord_mem_sphere (hpq := hpq) hp hq heq with h0 | h0
      · left; rw [ht, h0]; simp
      · right; rw [ht, h0]; simp
    · intro hz
      rcases hz with hz | hz
      · rw [hz]; exact ⟨hp, cS_left p q⟩
      · rw [hz]; exact ⟨hq, cS_right p q hpq⟩
  have hfrontΓ : frontier D ∩ Γ = {y} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzf, hzG⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      have hzD : z ∈ D := by
        rw [hΓdef, Set.mem_image] at hzG
        obtain ⟨w, hws, hwz⟩ := hzG
        have hw'cb : w ∈ Metric.closedBall (0:ℂ) 1 := segment_subset_closedBall hp hq hws
        have hwcase : w ∈ Metric.ball (0:ℂ) 1 ∨ w ∈ Metric.sphere (0:ℂ) 1 := by
          have := hw'cb; rwa [← Metric.ball_union_sphere] at this
        rcases hwcase with hwb | hwsph
        · rw [← hwz, ← hΨs]; exact ⟨w, hwb, rfl⟩
        · rcases segment_inter_sphere (hpq := hpq) hp hq hws hwsph with hh | hh
          · exact absurd (by rw [← hwz, hh, hy]) hne
          · exact absurd (by rw [← hwz, hh, hyq]) hne
      have hzf' := hzf
      rw [IsOpen.frontier_eq hDo] at hzf'
      exact hzf'.2 hzD
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hyfront, hyΓ⟩
  -- ## the main collapse step
  have hcollapsed : ∀ (P Q : Set ℂ), IsOpen P → IsOpen Q → Disjoint P Q → P ∪ Q = Γᶜ →
      frontier P = Γ → frontier Q = Γ → Ψ '' Wp ⊆ P → Ψ '' Wm ⊆ Q →
      Ψ '' Ap = {y} ∨ Ψ '' Am = {y} := by
    intro P Q hPo hQo hPQ hPQU hPf hQf hWpP hWmQ
    have hApP : Ψ '' Ap ⊆ P ∪ Γ := by
      calc Ψ '' Ap ⊆ Ψ '' closure Wp := Set.image_mono hApcl
        _ ⊆ closure (Ψ '' Wp) := (hΨc.mono hclWp).image_closure
        _ ⊆ closure P := closure_mono hWpP
        _ = P ∪ Γ := by rw [closure_eq_self_union_frontier, hPf]
    have hAmQ : Ψ '' Am ⊆ Q ∪ Γ := by
      calc Ψ '' Am ⊆ Ψ '' closure Wm := Set.image_mono hAmcl
        _ ⊆ closure (Ψ '' Wm) := (hΨc.mono hclWm).image_closure
        _ ⊆ closure Q := closure_mono hWmQ
        _ = Q ∪ Γ := by rw [closure_eq_self_union_frontier, hQf]
    have hBp_sub : Ψ '' Bp ⊆ P ∪ Γ := by
      rintro z ⟨a, ha, rfl⟩
      rw [hBp] at ha
      rcases lt_or_eq_of_le (show 0 ≤ cS p q a from ha.2) with hlt | heq
      · exact hApP ⟨a, by rw [hAp]; exact ⟨ha.1, hlt⟩, rfl⟩
      · right
        have hza : a ∈ Metric.sphere (0:ℂ) 1 ∩ {z | cS p q z = 0} := ⟨ha.1, heq.symm⟩
        rw [hszero] at hza
        rcases hza with hh | hh
        · rw [hh, ← hy]; exact hyΓ
        · rw [hh, hyq]; exact hyΓ
    have hBm_sub : Ψ '' Bm ⊆ Q ∪ Γ := by
      rintro z ⟨a, ha, rfl⟩
      rw [hBm] at ha
      rcases lt_or_eq_of_le (show cS p q a ≤ 0 from ha.2) with hlt | heq
      · exact hAmQ ⟨a, by rw [hAm]; exact ⟨ha.1, hlt⟩, rfl⟩
      · right
        have hza : a ∈ Metric.sphere (0:ℂ) 1 ∩ {z | cS p q z = 0} := ⟨ha.1, heq⟩
        rw [hszero] at hza
        rcases hza with hh | hh
        · rw [hh, ← hy]; exact hyΓ
        · rw [hh, hyq]; exact hyΓ
    have hBp_cl : IsClosed (Ψ '' Bp) := by
      have hBpc : IsCompact Bp :=
        (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset
          (by rw [hBp]; exact isClosed_sphere.inter (isClosed_le continuous_const (continuous_cS p q)))
          (fun z hz => Metric.sphere_subset_closedBall (by rw [hBp] at hz; exact hz.1))
      exact (hBpc.image_of_continuousOn
        (hΨc.mono (fun z hz => Metric.sphere_subset_closedBall (by rw [hBp] at hz; exact hz.1)))).isClosed
    have hBm_cl : IsClosed (Ψ '' Bm) := by
      have hBmc : IsCompact Bm :=
        (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset
          (by rw [hBm]; exact isClosed_sphere.inter (isClosed_le (continuous_cS p q) continuous_const))
          (fun z hz => Metric.sphere_subset_closedBall (by rw [hBm] at hz; exact hz.1))
      exact (hBmc.image_of_continuousOn
        (hΨc.mono (fun z hz => Metric.sphere_subset_closedBall (by rw [hBm] at hz; exact hz.1)))).isClosed
    have hSsub : frontier D \ {y} ⊆ Ψ '' Bp ∪ Ψ '' Bm := by
      intro z hz
      have hzf : z ∈ frontier D := hz.1
      rw [← hfront, Set.mem_image] at hzf
      obtain ⟨a, has, haz⟩ := hzf
      rcases le_total (cS p q a) 0 with hle | hge
      · right; exact ⟨a, by rw [hBm]; exact ⟨has, hle⟩, haz⟩
      · left; exact ⟨a, by rw [hBp]; exact ⟨has, hge⟩, haz⟩
    have hSdisj : (frontier D \ {y}) ∩ (Ψ '' Bp ∩ Ψ '' Bm) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzS, hzp, hzm⟩
      have hzΓ : z ∈ Γ := by
        rcases hBp_sub hzp with h | h
        · rcases hBm_sub hzm with h' | h'
          · exact absurd (Set.disjoint_left.mp hPQ h h') (by simp)
          · exact h'
        · exact h
      have : z ∈ ({y} : Set ℂ) := by rw [← hfrontΓ]; exact ⟨hzS.1, hzΓ⟩
      exact hzS.2 this
    have hSpre : IsPreconnected (frontier D \ {y}) :=
      Work.RPB1a.Caratheodory.isPreconnected_frontier_diff_singleton hJ hyfront
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hSpre) (Ψ '' Bp) (Ψ '' Bm)
        hBp_cl hBm_cl hSsub hSdisj with hSmem | hSmem
    · -- `S ⊆ Ψ '' Bp` forces `Ψ '' Am = {y}`
      right
      have hdisjBm : (frontier D \ {y}) ∩ Ψ '' Bm = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzS, hzm⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hSdisj) z ⟨hzS, hSmem hzS, hzm⟩
      have hBm_y : Ψ '' Bm ⊆ {y} := by
        intro z hz
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hzf : z ∈ frontier D := by
          obtain ⟨a, ha, rfl⟩ := hz
          rw [hBm] at ha; exact hmt ha.1
        exact (Set.eq_empty_iff_forall_notMem.mp hdisjBm) z ⟨⟨hzf, hne⟩, hz⟩
      obtain ⟨u, husph, hucs⟩ := (exists_cS_pos_and_neg hpq hp hq).2
      have huAm : u ∈ Am := by rw [hAm]; exact ⟨husph, hucs⟩
      have huBm : u ∈ Bm := by rw [hBm]; exact ⟨husph, le_of_lt hucs⟩
      have hyAm : y ∈ Ψ '' Am := by
        have h1 : Ψ u ∈ ({y} : Set ℂ) := hBm_y ⟨u, huBm, rfl⟩
        rw [Set.mem_singleton_iff] at h1
        exact ⟨u, huAm, h1⟩
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨hyAm, ?_⟩
      rintro b ⟨c, hc, hcb⟩
      have hcBm : c ∈ Bm := by
        rw [hBm]; rw [hAm] at hc
        exact ⟨hc.1, le_of_lt (show cS p q c < 0 from hc.2)⟩
      have h1 : Ψ c ∈ ({y} : Set ℂ) := hBm_y ⟨c, hcBm, rfl⟩
      rw [Set.mem_singleton_iff] at h1
      rw [← hcb, h1]
    · -- `S ⊆ Ψ '' Bm` forces `Ψ '' Ap = {y}`
      left
      have hdisjBp : (frontier D \ {y}) ∩ Ψ '' Bp = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzS, hzp⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hSdisj) z ⟨hzS, hzp, hSmem hzS⟩
      have hBp_y : Ψ '' Bp ⊆ {y} := by
        intro z hz
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hzf : z ∈ frontier D := by
          obtain ⟨a, ha, rfl⟩ := hz
          rw [hBp] at ha; exact hmt ha.1
        exact (Set.eq_empty_iff_forall_notMem.mp hdisjBp) z ⟨⟨hzf, hne⟩, hz⟩
      obtain ⟨u, husph, hucs⟩ := (exists_cS_pos_and_neg hpq hp hq).1
      have huAp : u ∈ Ap := by rw [hAp]; exact ⟨husph, hucs⟩
      have huBp : u ∈ Bp := by rw [hBp]; exact ⟨husph, le_of_lt hucs⟩
      have hyAp : y ∈ Ψ '' Ap := by
        have h1 : Ψ u ∈ ({y} : Set ℂ) := hBp_y ⟨u, huBp, rfl⟩
        rw [Set.mem_singleton_iff] at h1
        exact ⟨u, huAp, h1⟩
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨hyAp, ?_⟩
      rintro b ⟨c, hc, hcb⟩
      have hcBp : c ∈ Bp := by
        rw [hBp]; rw [hAp] at hc
        exact ⟨hc.1, le_of_lt (show 0 < cS p q c from hc.2)⟩
      have h1 : Ψ c ∈ ({y} : Set ℂ) := hBp_y ⟨c, hcBp, rfl⟩
      rw [Set.mem_singleton_iff] at h1
      rw [← hcb, h1]
  -- ## conclude
  rcases hWp_or with hWpP | hWpP <;> rcases hWm_or with hWmQ | hWmQ
  · exact absurd ⟨hWpP, hWmQ⟩ hnot_in
  · rcases hcollapsed ins out hio hoo hdisj hcov.symm hfi hfo hWpP hWmQ with hA | hA
    · obtain ⟨u, husph, hucs⟩ := (exists_cS_pos_and_neg hpq hp hq).1
      obtain ⟨δ, hδ, hδsub⟩ := isOpen_iff.mp
        (isOpen_lt continuous_const (continuous_cS p q)) u hucs
      exact ⟨u, husph, δ, hδ, fun z hzsph hzδ => by
        have hzT : z ∈ Ap := by
          rw [hAp]; exact ⟨hzsph, hδsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hzδ))⟩
        have h1 : Ψ z ∈ ({y} : Set ℂ) := by rw [← hA]; exact ⟨z, hzT, rfl⟩
        rw [Set.mem_singleton_iff] at h1
        rw [h1, hy]⟩
    · obtain ⟨u, husph, hucs⟩ := (exists_cS_pos_and_neg hpq hp hq).2
      obtain ⟨δ, hδ, hδsub⟩ := isOpen_iff.mp
        (isOpen_lt (continuous_cS p q) continuous_const) u hucs
      exact ⟨u, husph, δ, hδ, fun z hzsph hzδ => by
        have hzT : z ∈ Am := by
          rw [hAm]; exact ⟨hzsph, hδsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hzδ))⟩
        have h1 : Ψ z ∈ ({y} : Set ℂ) := by rw [← hA]; exact ⟨z, hzT, rfl⟩
        rw [Set.mem_singleton_iff] at h1
        rw [h1, hy]⟩
  · rcases hcollapsed out ins hoo hio hdisj.symm (by rw [Set.union_comm]; exact hcov.symm) hfo hfi hWpP hWmQ with hA | hA
    · obtain ⟨u, husph, hucs⟩ := (exists_cS_pos_and_neg hpq hp hq).1
      obtain ⟨δ, hδ, hδsub⟩ := isOpen_iff.mp
        (isOpen_lt continuous_const (continuous_cS p q)) u hucs
      exact ⟨u, husph, δ, hδ, fun z hzsph hzδ => by
        have hzT : z ∈ Ap := by
          rw [hAp]; exact ⟨hzsph, hδsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hzδ))⟩
        have h1 : Ψ z ∈ ({y} : Set ℂ) := by rw [← hA]; exact ⟨z, hzT, rfl⟩
        rw [Set.mem_singleton_iff] at h1
        rw [h1, hy]⟩
    · obtain ⟨u, husph, hucs⟩ := (exists_cS_pos_and_neg hpq hp hq).2
      obtain ⟨δ, hδ, hδsub⟩ := isOpen_iff.mp
        (isOpen_lt (continuous_cS p q) continuous_const) u hucs
      exact ⟨u, husph, δ, hδ, fun z hzsph hzδ => by
        have hzT : z ∈ Am := by
          rw [hAm]; exact ⟨hzsph, hδsub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hzδ))⟩
        have h1 : Ψ z ∈ ({y} : Set ℂ) := by rw [← hA]; exact ⟨z, hzT, rfl⟩
        rw [Set.mem_singleton_iff] at h1
        rw [h1, hy]⟩
  · exact absurd ⟨hWpP, hWmQ⟩ hnot_out


end Work.RPB.B1a
