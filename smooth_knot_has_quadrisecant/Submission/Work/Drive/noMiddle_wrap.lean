import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.separation_of_far_parameters
import Submission.Work.Drive.thinLocalRadial
import Submission.Work.Drive.chordFrame

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Elementary helpers for the wrap case

Two facts are used below.  First, an integer translate of a point `d` of `(0, period)` stays at
distance at least `min d (period - d)` from the origin.  Second, consequently the two parameter
classes of the endpoints of a wrap chord are at circle distance at least `η` as soon as the
parameter difference lies in `(η, period - η)`. -/

/-- An integer translate of a point of `(0, period)` stays at distance at least
`min d (period - d)` from the origin. -/
lemma nw_abs_sub_int_mul_period_ge {d : ℝ} (h0 : 0 < d) (h1 : d < period) (n : ℤ) :
    min d (period - d) ≤ |d - (n : ℝ) * period| := by
  rcases le_or_gt n 0 with hn | hn
  · have hn0 : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    have hnp : (n : ℝ) * period ≤ 0 := by nlinarith [period_pos]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - (n : ℝ) * period)]
    linarith [min_le_left d (period - d)]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnp : period ≤ (n : ℝ) * period := by nlinarith [period_pos]
    rw [abs_of_nonpos (by linarith : d - (n : ℝ) * period ≤ 0)]
    linarith [min_le_right d (period - d)]

/-- If `u - a ∈ (η, period - η)` then the two parameter classes of `u` and `a` are at circle
distance at least `η`. -/
lemma nw_dist_coe_ge {u a η : ℝ} (h0 : 0 < u - a) (h1 : u - a < period)
    (h2 : η ≤ u - a) (h3 : η ≤ period - (u - a)) :
    η ≤ dist ((u : ℝ) : AddCircle period) ((a : ℝ) : AddCircle period) := by
  have hd : dist ((u : ℝ) : AddCircle period) ((a : ℝ) : AddCircle period)
      = |(u - a) - ((round (period⁻¹ * (u - a)) : ℤ) : ℝ) * period| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact AddCircle.norm_eq period
  rw [hd]
  exact le_trans (le_min h2 h3) (nw_abs_sub_int_mul_period_ge h0 h1 _)

/-- **The wrap case of the `E3′` obstruction set is empty on the `C²`-ball** (lead's
`NOTES_LEAD_E3prime_wrap.md` §3, verbatim).  For a smooth `r` there are `εw, δw > 0` such that every
knot `r'` within the `C²`-`εw`-ball of `r` has: no point of the chord of a *wrap* pair (parameter
length `y` with `period - y ≤ δw`) lies on the open segment of the pair. -/
theorem noMiddle_wrap {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ εw δw : ℝ, 0 < εw ∧ 0 < δw ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < εw ∧ ‖velocity r' t - velocity r t‖ < εw ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < εw) →
        ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δw → a ≤ u → u ≤ a + y →
          r' u ∉ openSegment ℝ (r' a) (r' (a + y)) := by
  -- the three uniform inputs of the reference knot
  obtain ⟨εm, δm, hεm, hδm, hmono⟩ := exists_local_radial_mono hr
  obtain ⟨εs, hεs, hsep⟩ := separation_of_far_parameters hr
  obtain ⟨_m, M, _C, _hm, _hM, _hC, _hspd, hspdM, _hlip⟩ := exists_knot_c2_bounds hr
  set η : ℝ := δm / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  obtain ⟨sE, hsEpos, hsepE⟩ := hsep η hηpos
  set M' : ℝ := M + 1 with hM'def
  have hM'pos : 0 < M' := by rw [hM'def]; linarith
  refine ⟨min (min εm εs) 1, min η (sE / (2 * M')),
    lt_min (lt_min hεm hεs) one_pos,
    lt_min hηpos (div_pos hsEpos (by positivity)), ?_⟩
  intro r' hr' hclose a y u hy0 hylt hyδ hau huy
  -- the perturbed knot satisfies the three closeness conditions at every scale used
  have hw_m : min (min εm εs) 1 ≤ εm := le_trans (min_le_left _ _) (min_le_left _ _)
  have hw_s : min (min εm εs) 1 ≤ εs := le_trans (min_le_left _ _) (min_le_right _ _)
  have hw_1 : min (min εm εs) 1 ≤ 1 := min_le_right _ _
  have hclose_m : ∀ t : ℝ, ‖r' t - r t‖ < εm ∧ ‖velocity r' t - velocity r t‖ < εm ∧
      ‖deriv (deriv r') t - deriv (deriv r) t‖ < εm := fun t =>
    ⟨lt_of_lt_of_le (hclose t).1 hw_m, lt_of_lt_of_le (hclose t).2.1 hw_m,
      lt_of_lt_of_le (hclose t).2.2 hw_m⟩
  have hclose_s : ∀ t : ℝ, ‖r' t - r t‖ < εs ∧ ‖velocity r' t - velocity r t‖ < εs := fun t =>
    ⟨lt_of_lt_of_le (hclose t).1 hw_s, lt_of_lt_of_le (hclose t).2.1 hw_s⟩
  obtain ⟨hmonoF, hmonoB⟩ := hmono r' hr' hclose_m
  -- the uniform speed bound of the perturbed knot, hence its Lipschitz constant `M'`
  have hvel' : ∀ t : ℝ, ‖velocity r' t‖ ≤ M' := by
    intro t
    have h1 : ‖velocity r t‖ ≤ M := hspdM t
    have h2 : ‖velocity r' t - velocity r t‖ < 1 := lt_of_lt_of_le (hclose t).2.1 hw_1
    have h3 : ‖velocity r' t‖ ≤ ‖velocity r t‖ + ‖velocity r' t - velocity r t‖ := by
      have h4 := norm_add_le (velocity r t) (velocity r' t - velocity r t)
      rwa [add_sub_cancel] at h4
    rw [hM'def]
    linarith
  have hlip' : ∀ s t : ℝ, ‖r' t - r' s‖ ≤ M' * |t - s| :=
    norm_sub_le_of_velocity_bound hr'.smooth hvel'
  -- the wrap length and the periodicity of the two endpoints
  set e : ℝ := period - y with hedef
  have he0 : 0 < e := by rw [hedef]; linarith
  have heδ : e ≤ min η (sE / (2 * M')) := hyδ
  have heη : e ≤ η := le_trans heδ (min_le_left _ _)
  have heE : e ≤ sE / (2 * M') := le_trans heδ (min_le_right _ _)
  have hBeq : r' (a + y) = r' (a - e) := by
    have harg : a - e + period = a + y := by rw [hedef]; ring
    rw [← harg]
    exact hr'.periodic (a - e)
  intro hX
  -- the two endpoints of a genuine secant are distinct
  have hAB : r' a ≠ r' (a + y) := by
    intro hab
    have h1 := knotMap_eq_of_periodic hr'.periodic a
    have h2 := knotMap_eq_of_periodic hr'.periodic (a + y)
    have h3 : ((a : ℝ) : AddCircle period) = (((a + y : ℝ)) : AddCircle period) :=
      knotMap_injective hr' (h1.trans (hab.trans h2.symm))
    exact (coe_ne_coe_of_lt (x := a) hy0 hylt) h3
  have hXneA : r' u ≠ r' a := (ne_left_right_of_mem_openSegment hAB hX).1
  have hXneB : r' u ≠ r' (a + y) := (ne_left_right_of_mem_openSegment hAB hX).2
  obtain ⟨α, β, hα0, hβ0, hαβ, hXeq⟩ := hX
  -- the two strict inequalities of a strict middle point `(★)`
  have hβeq : β = 1 - α := by linarith
  have hαeq : α = 1 - β := by linarith
  have hsub1 : r' u - r' a = β • (r' (a + y) - r' a) := by
    rw [← hXeq, smul_sub, hαeq, sub_smul, one_smul]
    abel
  have hnorm1 : ‖r' u - r' a‖ = β * ‖r' (a + y) - r' a‖ := by
    rw [hsub1, norm_smul, Real.norm_eq_abs, abs_of_pos hβ0]
  have hBApos : 0 < ‖r' (a + y) - r' a‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hAB)
  have hβlt1 : β < 1 := by linarith
  have hstarA : ‖r' u - r' a‖ < ‖r' (a + y) - r' a‖ := by
    rw [hnorm1]
    nlinarith [hBApos, hβlt1]
  have hsub2 : r' u - r' (a + y) = α • (r' a - r' (a + y)) := by
    rw [← hXeq, smul_sub, hβeq, sub_smul, one_smul]
    abel
  have hnorm2 : ‖r' u - r' (a + y)‖ = α * ‖r' (a + y) - r' a‖ := by
    rw [hsub2, norm_smul, Real.norm_eq_abs, abs_of_pos hα0, norm_sub_rev]
  have hαlt1 : α < 1 := by linarith
  have hstarB : ‖r' u - r' (a + y)‖ < ‖r' (a + y) - r' a‖ := by
    rw [hnorm2]
    nlinarith [hBApos, hαlt1]
  -- the case analysis: `u` is near `a`, near `a + y`, or genuinely far
  rcases le_or_gt (u - a) η with hc1 | hc1
  · -- `u` is near `a`: forward radial monotonicity from the base `a - e`
    have hua : a < u := by
      rcases lt_or_eq_of_le hau with h | h
      · exact h
      · exact absurd (show r' u = r' a by rw [← h]) hXneA
    have hss' : e < e + (u - a) := by linarith
    have hsd : e + (u - a) ≤ δm := by linarith [heη, hc1, hηdef]
    have h1 := hmonoF (a - e) e (e + (u - a)) (le_of_lt he0) hss' hsd
    have hla : (a - e) + e = a := by ring
    have hra : (a - e) + (e + (u - a)) = u := by ring
    rw [hla, hra, ← hBeq] at h1
    rw [norm_sub_rev (r' a) (r' (a + y))] at h1
    linarith [h1, hstarB]
  · rcases le_or_gt (a + y - u) η with hc2 | hc2
    · -- `u` is near `a + y`: backward radial monotonicity from the base `a`
      have hut : u < a + y := by
        rcases lt_or_eq_of_le huy with h | h
        · exact h
        · exact absurd (show r' u = r' (a + y) by rw [h]) hXneB
      have hss' : e < e + (a + y - u) := by linarith
      have hsd : e + (a + y - u) ≤ δm := by linarith [heη, hc2, hηdef]
      have h2 := hmonoB a e (e + (a + y - u)) (le_of_lt he0) hss' hsd
      have harg : a - (e + (a + y - u)) = u - period := by rw [hedef]; ring
      have hper : r' (u - period) = r' u := by
        have h := hr'.periodic (u - period)
        rw [show u - period + period = u from by ring] at h
        exact h.symm
      rw [harg, hper, ← hBeq] at h2
      linarith [h2, hstarA]
    · -- `u` is genuinely far from both endpoints: uniform separation wins
      have hd0 : 0 < u - a := by linarith [hc1, hηpos]
      have hd1 : u - a < period := by linarith [huy, hylt]
      have hd3 : η ≤ period - (u - a) := by linarith [hc2, he0, hedef]
      have hdist : η ≤ dist ((u : ℝ) : AddCircle period) ((a : ℝ) : AddCircle period) :=
        nw_dist_coe_ge hd0 hd1 (le_of_lt hc1) hd3
      have hsep' := hsepE r' hr' hclose_s ((u : ℝ) : AddCircle period)
        ((a : ℝ) : AddCircle period) hdist
      rw [knotMap_eq_of_periodic hr'.periodic u,
        knotMap_eq_of_periodic hr'.periodic a] at hsep'
      have hBA : ‖r' (a + y) - r' a‖ ≤ M' * e := by
        have h1 : ‖r' (a - e) - r' a‖ ≤ M' * e := by
          have h0' := hlip' (a - e) a
          rw [show a - (a - e) = e from by ring, abs_of_pos he0, norm_sub_rev] at h0'
          exact h0'
        rwa [← hBeq] at h1
      have heE' : M' * e ≤ sE / 2 := by
        have h2 : M' * e ≤ M' * (sE / (2 * M')) := mul_le_mul_of_nonneg_left heE (le_of_lt hM'pos)
        have h3 : M' * (sE / (2 * M')) = sE / 2 := by
          field_simp
        linarith [h2, h3]
      have hsmall : ‖r' u - r' a‖ < sE := by linarith [hstarA, hBA, heE', hsEpos]
      linarith [hsep', hsmall]

end Work.Drive

/-- The same statement, exposed under the name at which it was requested. -/
theorem noMiddle_wrap {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ εw δw : ℝ, 0 < εw ∧ 0 < δw ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < εw ∧ ‖velocity r' t - velocity r t‖ < εw ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < εw) →
        ∀ a y u : ℝ, 0 < y → y < period → period - y ≤ δw → a ≤ u → u ≤ a + y →
          r' u ∉ openSegment ℝ (r' a) (r' (a + y)) :=
  _root_.Work.Drive.Work.Drive.noMiddle_wrap hr

end Work.Drive
