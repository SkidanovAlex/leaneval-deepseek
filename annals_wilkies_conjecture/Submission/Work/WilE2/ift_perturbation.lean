import Mathlib

namespace Work.WilE2

open scoped Classical Topology
open Classical

/-- **Inverse function theorem, perturbation form.**

Let `Φ : (Fin m → ℝ) → (Fin m → ℝ)` be `C¹` and let `T` be a finite set of zeros of `Φ`
at which the Jacobian determinant of `Φ` does not vanish. Then every point `y` sufficiently
close to `0` has at least `T.card` preimages under `Φ`:
there is a `Finset t` with `t.card = T.card` such that `Φ z = y` for every `z ∈ t`.

The proof picks pairwise disjoint small balls around the points of `T` (the radius function
`r` is one third of the minimal pairwise distance), uses `HasStrictFDerivAt.map_nhds_eq_of_equiv`
to see that `Φ` maps a neighbourhood of each `z ∈ T` onto a neighbourhood of `Φ z = 0`,
takes a uniform radius `ρ` as the minimum of the resulting radii, and chooses one preimage of
`y` in each of the balls; pairwise disjointness gives distinctness, hence the cardinality. -/
theorem ift_perturbation {m : ℕ} (Φ : (Fin m → ℝ) → (Fin m → ℝ)) (hΦ : ContDiff ℝ 1 Φ)
    (T : Finset (Fin m → ℝ)) (hT : ∀ z ∈ T, Φ z = 0) (hnd : ∀ z ∈ T, (fderiv ℝ Φ z).det ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : Fin m → ℝ, dist y 0 < ρ →
      ∃ t : Finset (Fin m → ℝ), t.card = T.card ∧ ∀ z ∈ t, Φ z = y := by
  -- Radii of pairwise disjoint balls around the points of `T`.
  set r : (Fin m → ℝ) → ℝ := (fun z =>
    if h : (T.erase z).Nonempty then (T.erase z).inf' h (fun w => dist z w) / 3 else 1) with hr
  have hrpos : ∀ z : Fin m → ℝ, 0 < r z := by
    intro z
    simp only [hr]
    split_ifs with h
    · apply div_pos _ (by norm_num)
      rw [Finset.lt_inf'_iff]
      intro b hb
      have hbz : b ≠ z := (Finset.mem_erase.mp hb).1
      exact dist_pos.mpr (Ne.symm hbz)
    · norm_num
  -- Local surjectivity of `Φ` near each `z ∈ T`.
  have hsurj : ∀ z ∈ T, ∃ δ : ℝ, 0 < δ ∧ Metric.ball 0 δ ⊆ Φ '' Metric.ball z (r z) := by
    intro z hz
    have hstrict : HasStrictFDerivAt Φ (fderiv ℝ Φ z) z :=
      (hΦ.contDiffAt).hasStrictFDerivAt (by norm_num)
    have hmap : Filter.map Φ (𝓝 z) = 𝓝 (0 : Fin m → ℝ) := by
      have := hstrict.map_nhds_eq_of_equiv
        (f' := (fderiv ℝ Φ z).toContinuousLinearEquivOfDetNeZero (hnd z hz))
      rwa [hT z hz] at this
    have hmem : Φ '' Metric.ball z (r z) ∈ 𝓝 (0 : Fin m → ℝ) := by
      have hb : Metric.ball z (r z) ∈ 𝓝 z := Metric.ball_mem_nhds z (hrpos z)
      have : Φ '' Metric.ball z (r z) ∈ Filter.map Φ (𝓝 z) :=
        Filter.mem_map.mpr (Filter.mem_of_superset hb (fun x hx => ⟨x, hx, rfl⟩))
      rwa [hmap] at this
    exact Metric.mem_nhds_iff.mp hmem
  -- A choice of radii, made globally so that a uniform `ρ` can be taken.
  set δf : (Fin m → ℝ) → ℝ :=
    (fun z => if hz : z ∈ T then Classical.choose (hsurj z hz) else 1) with hδfeq
  have hδfpos : ∀ z ∈ T, 0 < δf z := by
    intro z hz
    simp only [hδfeq]
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (hsurj z hz)).1
  have hδfsub : ∀ z ∈ T, Metric.ball 0 (δf z) ⊆ Φ '' Metric.ball z (r z) := by
    intro z hz
    simp only [hδfeq]
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (hsurj z hz)).2
  -- The uniform radius.
  set ρ : ℝ := (if h : T.Nonempty then T.inf' h δf else 1) with hρ
  have hρpos : 0 < ρ := by
    simp only [hρ]
    split_ifs with h
    · exact (Finset.lt_inf'_iff h).mpr (fun b hb => hδfpos b hb)
    · norm_num
  refine ⟨ρ, hρpos, fun y hy => ?_⟩
  have hρle : ∀ z ∈ T, ρ ≤ δf z := by
    intro z hz
    simp only [hρ]
    split_ifs with h
    · exact Finset.inf'_le δf hz
    · exact absurd ⟨z, hz⟩ h
  have hex : ∀ z ∈ T, ∃ w, w ∈ Metric.ball z (r z) ∧ Φ w = y := by
    intro z hz
    have hlt : dist y 0 < δf z := lt_of_lt_of_le hy (hρle z hz)
    have hyb : y ∈ Metric.ball 0 (δf z) := Metric.mem_ball.mpr hlt
    obtain ⟨w, hw, hwy⟩ := hδfsub z hz hyb
    exact ⟨w, hw, hwy⟩
  -- Choose one preimage of `y` in each ball, and show the choices are distinct.
  set wf : (Fin m → ℝ) → (Fin m → ℝ) :=
    (fun z => if hz : z ∈ T then Classical.choose (hex z hz) else z) with hwf
  have hwfmem : ∀ z ∈ T, wf z ∈ Metric.ball z (r z) := by
    intro z hz
    simp only [hwf]
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (hex z hz)).1
  have hwfΦ : ∀ z ∈ T, Φ (wf z) = y := by
    intro z hz
    simp only [hwf]
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (hex z hz)).2
  -- The balls `Metric.ball z (r z)` are pairwise disjoint.
  have hdisj : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' →
      ∀ x, x ∈ Metric.ball z (r z) → x ∈ Metric.ball z' (r z') → False := by
    intro z hz z' hz' hne x hx hx'
    have hzz' : z' ∈ T.erase z := Finset.mem_erase.mpr ⟨Ne.symm hne, hz'⟩
    have hne1 : (T.erase z).Nonempty := ⟨z', hzz'⟩
    have hrz : r z ≤ dist z z' / 3 := by
      simp only [hr]
      rw [dite_eq_left hne1]
      have := Finset.inf'_le (s := T.erase z) (f := fun w => dist z w) hzz'
      linarith
    have hzz : z ∈ T.erase z' := Finset.mem_erase.mpr ⟨hne, hz⟩
    have hne2 : (T.erase z').Nonempty := ⟨z, hzz⟩
    have hrz' : r z' ≤ dist z' z / 3 := by
      simp only [hr]
      rw [dite_eq_left hne2]
      have := Finset.inf'_le (s := T.erase z') (f := fun w => dist z' w) hzz
      linarith
    have hd1 : dist x z < r z := Metric.mem_ball.mp hx
    have hd2 : dist x z' < r z' := Metric.mem_ball.mp hx'
    have ht : dist z z' ≤ dist x z + dist x z' := by
      calc dist z z' ≤ dist z x + dist x z' := dist_triangle z x z'
        _ = dist x z + dist x z' := by rw [dist_comm z x]
    have hdd : dist z' z = dist z z' := dist_comm z' z
    linarith [ht, hd1, hd2, hrz, hrz', hdd, dist_nonneg (x := z) (y := z')]
  have hwf_inj : Set.InjOn wf ↑T := by
    intro z hz z' hz' heq
    by_contra hne
    have b1 := hwfmem z hz
    have b2 := hwfmem z' hz'
    rw [heq] at b1
    exact hdisj z hz z' hz' hne (wf z') b1 b2
  refine ⟨T.image wf, ?_, ?_⟩
  · exact Finset.card_image_of_injOn hwf_inj
  · intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨z, hz, rfl⟩ := hu
    exact hwfΦ z hz

end Work.WilE2
