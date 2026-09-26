import Mathlib

namespace Work.Smooth.BoxGeneric.LocalArc

open Filter

/-- **The implicit function of a strictly monotone family.**  Let `F : ℝ × ℝ → ℝ` be continuous,
`Rx, Ry > 0`, `F (0,0) = 0`, `F` negative on the left face `x = -Rx` and positive on the right
face `x = Rx` of the box `[-Rx,Rx] × [-Ry,Ry]`, and suppose that for every `y ∈ [-Ry,Ry]` the
partial map `x ↦ F (x,y)` is strictly increasing on `[-Rx,Rx]`.  Then the zero set of `F` in the
box is the graph `x = ψ y` of a function `ψ` which is continuous on the open interval `(-Ry,Ry)`,
and `F (x,y) ≤ 0 ↔ x ≤ ψ y` (resp. `F (x,y) = 0 ↔ x = ψ y`) for `|x| ≤ Rx`, `|y| ≤ Ry`. -/
theorem exists_root_of_mono {F : ℝ × ℝ → ℝ} (hFc : Continuous F) {Rx Ry : ℝ}
    (hRx : 0 < Rx) (hRy : 0 < Ry) (hF0 : F (0, 0) = 0)
    (hneg : ∀ y : ℝ, |y| ≤ Ry → F (-Rx, y) < 0)
    (hpos : ∀ y : ℝ, |y| ≤ Ry → 0 < F (Rx, y))
    (hmono : ∀ y : ℝ, |y| ≤ Ry → StrictMonoOn (fun x : ℝ => F (x, y)) (Set.Icc (-Rx) Rx)) :
    ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧ ContinuousOn ψ (Set.Ioo (-Ry) Ry) ∧
      (∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ F (ψ y, y) = 0) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y)) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y)) := by
  classical
  have hcont : ∀ y : ℝ, Continuous (fun x : ℝ => F (x, y)) := fun y =>
    hFc.comp (continuous_id.prodMk continuous_const)
  -- existence and uniqueness of the zero of `x ↦ F (x,y)` in `[-Rx,Rx]`
  have hroot : ∀ y : ℝ, |y| ≤ Ry → ∃ x : ℝ, x ∈ Set.Icc (-Rx) Rx ∧ F (x, y) = 0 ∧
      ∀ z : ℝ, z ∈ Set.Icc (-Rx) Rx → F (z, y) = 0 → z = x := by
    intro y hy
    have hle : -Rx ≤ Rx := by linarith
    have h0 : (0:ℝ) ∈ Set.Icc (F (-Rx, y)) (F (Rx, y)) :=
      ⟨le_of_lt (hneg y hy), le_of_lt (hpos y hy)⟩
    have himage : (0:ℝ) ∈ (fun x : ℝ => F (x, y)) '' Set.Icc (-Rx) Rx :=
      intermediate_value_Icc hle (hcont y).continuousOn h0
    obtain ⟨x, hxIcc, hx0⟩ := himage
    exact ⟨x, hxIcc, hx0, fun z hzIcc hz0 =>
      (hmono y hy).injOn hzIcc hxIcc (by simp only [hz0, hx0])⟩
  -- the same, made into a total statement so that we may use `Classical.choose`
  have hroot' : ∀ y : ℝ, ∃ x : ℝ,
      (|y| ≤ Ry → x ∈ Set.Icc (-Rx) Rx ∧ F (x, y) = 0 ∧
        ∀ z : ℝ, z ∈ Set.Icc (-Rx) Rx → F (z, y) = 0 → z = x) := by
    intro y
    by_cases h : |y| ≤ Ry
    · obtain ⟨x, hx⟩ := hroot y h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun hh => absurd hh h⟩
  let ψ : ℝ → ℝ := fun y => Classical.choose (hroot' y)
  have hψ_spec : ∀ y : ℝ, |y| ≤ Ry → ψ y ∈ Set.Icc (-Rx) Rx ∧ F (ψ y, y) = 0 ∧
      ∀ z : ℝ, z ∈ Set.Icc (-Rx) Rx → F (z, y) = 0 → z = ψ y := by
    intro y hy
    exact Classical.choose_spec (hroot' y) hy
  have hψ0 : ψ 0 = 0 := by
    have h0le : |(0:ℝ)| ≤ Ry := by rw [abs_zero]; exact le_of_lt hRy
    have h0mem : (0:ℝ) ∈ Set.Icc (-Rx) Rx := ⟨by linarith, le_of_lt hRx⟩
    have h := (hψ_spec 0 h0le).2.2 0 h0mem hF0
    exact h.symm
  have hroot_prop : ∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ F (ψ y, y) = 0 := by
    intro y hy
    have h := hψ_spec y hy
    exact ⟨abs_le.mpr ⟨h.1.1, h.1.2⟩, h.2.1⟩
  have hle_iff : ∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y) := by
    intro x y hx hy
    have hxIcc : x ∈ Set.Icc (-Rx) Rx := ⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩
    have hψIcc : ψ y ∈ Set.Icc (-Rx) Rx := (hψ_spec y hy).1
    have hFψ : F (ψ y, y) = 0 := (hψ_spec y hy).2.1
    have h := (hmono y hy).le_iff_le hxIcc hψIcc
    rwa [hFψ] at h
  have heq_iff : ∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y) := by
    intro x y hx hy
    have hxIcc : x ∈ Set.Icc (-Rx) Rx := ⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩
    have hψIcc : ψ y ∈ Set.Icc (-Rx) Rx := (hψ_spec y hy).1
    have hFψ : F (ψ y, y) = 0 := (hψ_spec y hy).2.1
    constructor
    · intro h
      exact (hmono y hy).injOn hxIcc hψIcc (by rw [h, hFψ])
    · intro h
      rw [h]; exact hFψ
  have hcontψ : ContinuousOn ψ (Set.Ioo (-Ry) Ry) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    have hb_abs : |b| < Ry := abs_lt.mpr hb
    have hb_le : |b| ≤ Ry := le_of_lt hb_abs
    have hbspec := hψ_spec b hb_le
    have hxIcc : ψ b ∈ Set.Icc (-Rx) Rx := hbspec.1
    have hFx : F (ψ b, b) = 0 := hbspec.2.1
    have hx_gt : -Rx < ψ b := by
      rcases lt_or_eq_of_le hxIcc.1 with h | h
      · exact h
      · exfalso
        have h' : F (-Rx, b) < 0 := hneg b hb_le
        rw [h] at h'
        rw [hFx] at h'
        exact lt_irrefl 0 h'
    have hx_lt : ψ b < Rx := by
      rcases lt_or_eq_of_le hxIcc.2 with h | h
      · exact h
      · exfalso
        have h' : 0 < F (Rx, b) := hpos b hb_le
        rw [← h] at h'
        rw [hFx] at h'
        exact lt_irrefl 0 h'
    -- the two auxiliary abscissae `a < ψ b < b'`, both inside `[-Rx,Rx]`
    set a : ℝ := max (-Rx) (ψ b - ε) with ha_def
    set b' : ℝ := min Rx (ψ b + ε) with hb'_def
    have ha_lt : a < ψ b := by
      rw [ha_def]; exact max_lt hx_gt (by linarith)
    have hb'_gt : ψ b < b' := by
      rw [hb'_def]; exact lt_min hx_lt (by linarith)
    have haIcc : a ∈ Set.Icc (-Rx) Rx := by
      rw [ha_def]
      exact ⟨le_max_left _ _, le_of_lt (max_lt (by linarith) (by linarith))⟩
    have hb'Icc : b' ∈ Set.Icc (-Rx) Rx := by
      rw [hb'_def]
      exact ⟨le_of_lt (lt_min (by linarith) (by linarith)), min_le_left _ _⟩
    have ha_abs : |a| ≤ Rx := abs_le.mpr haIcc
    have hb'_abs : |b'| ≤ Rx := abs_le.mpr hb'Icc
    have hFa : F (a, b) < 0 := by
      have h := ((hmono b hb_le).lt_iff_lt haIcc hxIcc).mpr ha_lt
      rwa [hFx] at h
    have hFb' : 0 < F (b', b) := by
      have h := ((hmono b hb_le).lt_iff_lt hxIcc hb'Icc).mpr hb'_gt
      rw [hFx] at h
      exact h
    -- `F a ·` stays negative and `F b' ·` stays positive near `b`
    have hcont_a : Continuous (fun y : ℝ => F (a, y)) :=
      hFc.comp (continuous_const.prodMk continuous_id)
    have hcont_b' : Continuous (fun y : ℝ => F (b', y)) :=
      hFc.comp (continuous_const.prodMk continuous_id)
    have hev_a : ∀ᶠ y in nhds b, F (a, y) < 0 :=
      hcont_a.continuousAt (isOpen_Iio.mem_nhds hFa)
    have hev_b' : ∀ᶠ y in nhds b, 0 < F (b', y) :=
      hcont_b'.continuousAt (isOpen_Ioi.mem_nhds hFb')
    obtain ⟨δa, hδa_pos, hδa⟩ := Metric.eventually_nhds_iff.mp hev_a
    obtain ⟨δb, hδb_pos, hδb⟩ := Metric.eventually_nhds_iff.mp hev_b'
    refine ⟨min δa δb, lt_min hδa_pos hδb_pos, ?_⟩
    intro a' ha' hdist
    have ha'_le : |a'| ≤ Ry := le_of_lt (abs_lt.mpr ha')
    have hFa' : F (a, a') < 0 :=
      hδa (lt_of_lt_of_le hdist (min_le_left δa δb))
    have hFb'' : 0 < F (b', a') :=
      hδb (lt_of_lt_of_le hdist (min_le_right δa δb))
    have hale : a ≤ ψ a' := (hle_iff a a' ha_abs ha'_le).mp (le_of_lt hFa')
    have halt : a < ψ a' := by
      refine lt_of_le_of_ne hale ?_
      intro h
      have hzero : F (a, a') = 0 := by rw [h]; exact (hψ_spec a' ha'_le).2.1
      linarith
    have hb'lt : ψ a' < b' := by
      by_contra hcon
      have hcon' : b' ≤ ψ a' := not_lt.mp hcon
      have hle0 : F (b', a') ≤ 0 := (hle_iff b' a' hb'_abs ha'_le).mpr hcon'
      linarith
    have ha_ge : ψ b - ε ≤ a := by rw [ha_def]; exact le_max_right _ _
    have hb'_le : b' ≤ ψ b + ε := by rw [hb'_def]; exact min_le_right _ _
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  exact ⟨ψ, hψ0, hcontψ, hroot_prop, hle_iff, heq_iff⟩

end Work.Smooth.BoxGeneric.LocalArc
