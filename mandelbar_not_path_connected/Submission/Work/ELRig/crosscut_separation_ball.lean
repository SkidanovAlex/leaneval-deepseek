import Mathlib
import Submission.Work.Topology.crosscut_axis_separation_v2
import Submission.Work.Topology.disc_cap_subset_boundedSide
import Submission.Work.TopJordan.isJordanCurve_of_two_arcs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Metric
open scoped Topology

namespace Work.ELRig

noncomputable section

/-! ## Elementary real analysis: sign of an endpoint

If a continuous function is strictly positive on an open interval, it is nonnegative at both
endpoints. -/

private lemma nonneg_of_Ioo_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hpos : ∀ t ∈ Set.Ioo a b, 0 < f t) :
    0 ≤ f a := by
  by_contra h
  push_neg at h
  obtain ⟨m, hm1, hm2⟩ := exists_between hab
  have hfm : 0 < f m := hpos m ⟨hm1, hm2⟩
  have hcont : ContinuousOn f (Set.Icc a m) :=
    hfc.mono (fun x hx => ⟨hx.1, hx.2.trans hm2.le⟩)
  have hpc : IsPreconnected (f '' Set.Icc a m) :=
    IsPreconnected.image isPreconnected_Icc f hcont
  have h0mem : (0:ℝ) ∈ f '' Set.Icc a m :=
    hpc.Icc_subset ⟨a, ⟨le_refl a, hm1.le⟩, rfl⟩ ⟨m, ⟨hm1.le, le_refl m⟩, rfl⟩
      (Set.mem_Icc.mpr ⟨le_of_lt h, le_of_lt hfm⟩)
  obtain ⟨x, hx, hx0⟩ := h0mem
  rcases eq_or_lt_of_le hx.1 with hxa | hxgt
  · rw [← hxa] at hx0; linarith
  · rcases eq_or_lt_of_le hx.2 with hxm | hxlt
    · rw [hxm] at hx0; linarith
    · exact absurd hx0 (ne_of_gt (hpos x ⟨hxgt, lt_trans hxlt hm2⟩))

private lemma nonneg_of_Ioo_pos' {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hpos : ∀ t ∈ Set.Ioo a b, 0 < f t) :
    0 ≤ f b := by
  by_contra h
  push_neg at h
  obtain ⟨m, hm1, hm2⟩ := exists_between hab
  have hfm : 0 < f m := hpos m ⟨hm1, hm2⟩
  have hcont : ContinuousOn f (Set.Icc m b) :=
    hfc.mono (fun x hx => ⟨hm1.le.trans hx.1, hx.2⟩)
  have hpc : IsPreconnected (f '' Set.Icc m b) :=
    IsPreconnected.image isPreconnected_Icc f hcont
  have h0mem : (0:ℝ) ∈ f '' Set.Icc m b :=
    hpc.Icc_subset ⟨b, ⟨hm2.le, le_refl b⟩, rfl⟩ ⟨m, ⟨le_refl m, hm2.le⟩, rfl⟩
      (Set.mem_Icc.mpr ⟨le_of_lt h, le_of_lt hfm⟩)
  obtain ⟨x, hx, hx0⟩ := h0mem
  rcases eq_or_lt_of_le hx.2 with hxb | hxlt
  · rw [hxb] at hx0; linarith
  · rcases eq_or_lt_of_le hx.1 with hxm | hxgt
    · rw [← hxm] at hx0; linarith
    · exact absurd hx0 (ne_of_gt (hpos x ⟨lt_trans hm1 hxgt, hxlt⟩))

private lemma nonpos_of_Ioo_neg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hneg : ∀ t ∈ Set.Ioo a b, f t < 0) :
    f b ≤ 0 := by
  have h : 0 ≤ (fun t => -f t) b :=
    nonneg_of_Ioo_pos' (f := fun t => -f t) hab hfc.neg (fun t ht => by
      simpa using hneg t ht)
  simpa using h

/-! ## The similarity that straightens the situation

`sim p ρ z = -i (z - p) / ρ` maps the disc of centre `p` and radius `ρ` onto the unit disc,
carries `p` to `0`, and carries the vertical diameter `p ± i t ρ` onto the real diameter `±t`. -/

private def sim (p : ℂ) (ρ : ℝ) (z : ℂ) : ℂ := -Complex.I * (z - p) / (ρ : ℂ)

private lemma sim_cont (p : ℂ) (ρ : ℝ) : Continuous (sim p ρ) := by
  unfold sim; fun_prop

private lemma sim_norm {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    ‖sim p ρ z‖ = dist z p / ρ := by
  rw [sim, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos hρ, Complex.dist_eq]

private lemma sim_injective {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) : Function.Injective (sim p ρ) := by
  intro a b hab
  have hne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
  have h := congrArg (fun w => w * (ρ:ℂ)) hab
  simp only [sim] at h
  rw [div_mul_cancel₀ _ hne, div_mul_cancel₀ _ hne] at h
  have hI : (-Complex.I : ℂ) ≠ 0 := by simpa using Complex.I_ne_zero
  have h2 : a - p = b - p := mul_left_cancel₀ hI h
  have h3 : (a - p) + p = (b - p) + p := by rw [h2]
  simpa using h3

private lemma sim_mem_ball {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    sim p ρ z ∈ Metric.ball (0:ℂ) 1 ↔ z ∈ Metric.ball p ρ := by
  rw [Metric.mem_ball, dist_zero_right, sim_norm hρ, div_lt_one hρ, Metric.mem_ball]

private lemma sim_mem_sphere {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    sim p ρ z ∈ Metric.sphere (0:ℂ) 1 ↔ z ∈ Metric.sphere p ρ := by
  rw [Metric.mem_sphere, dist_zero_right, sim_norm hρ, div_eq_one_iff_eq (ne_of_gt hρ),
    Metric.mem_sphere]

private lemma sim_re {p : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) (z : ℂ) :
    (sim p ρ z).re = (z - p).im / ρ := by
  simp only [sim]
  rw [Complex.div_re]
  rw [show (-Complex.I * (z-p)).re = (z-p).im from by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]]
  rw [show (-Complex.I * (z-p)).im = -(z-p).re from by
        simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

private lemma sim_im {p : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) (z : ℂ) :
    (sim p ρ z).im = -((z - p).re) / ρ := by
  simp only [sim]
  rw [Complex.div_im]
  rw [show (-Complex.I * (z-p)).re = (z-p).im from by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re]]
  rw [show (-Complex.I * (z-p)).im = -(z-p).re from by
        simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im]]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

private lemma sim_im_eq_zero {p : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) (z : ℂ) :
    (sim p ρ z).im = 0 ↔ z.re = p.re := by
  rw [sim_im hρ, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have h' : -((z - p).re) = 0 := by simpa using h
      simp only [neg_eq_zero, Complex.sub_re] at h'
      linarith
    · exact absurd h hρ
  · intro h
    left
    have : (z - p).re = 0 := by simp only [Complex.sub_re]; linarith
    rw [this]; simp

private lemma sim_p {p : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) : sim p ρ p = 0 := by
  apply Complex.ext
  · rw [sim_re hρ, Complex.zero_re]; simp
  · rw [sim_im hρ, Complex.zero_im]; simp

private lemma sim_pt {p : ℂ} {ρ t : ℝ} (hρ : ρ ≠ 0) :
    sim p ρ (p + ((t:ℂ) * (ρ:ℂ)) * Complex.I) = (t:ℂ) := by
  rw [show (t:ℂ) * (ρ:ℂ) = ((t*ρ : ℝ) : ℂ) from (Complex.ofReal_mul t ρ).symm]
  apply Complex.ext
  · rw [sim_re hρ, Complex.ofReal_re]
    rw [show (p + ((t*ρ:ℝ):ℂ) * Complex.I - p).im = t*ρ from by
      simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]]
    field_simp
  · rw [sim_im hρ, Complex.ofReal_im]
    rw [show (p + ((t*ρ:ℝ):ℂ) * Complex.I - p).re = 0 from by
      simp [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]]
    simp

private lemma sim_mt {p : ℂ} {ρ t : ℝ} (hρ : ρ ≠ 0) :
    sim p ρ (p - ((t:ℂ) * (ρ:ℂ)) * Complex.I) = -(t:ℂ) := by
  rw [show (t:ℂ) * (ρ:ℂ) = ((t*ρ : ℝ) : ℂ) from (Complex.ofReal_mul t ρ).symm]
  apply Complex.ext
  · rw [sim_re hρ]
    rw [show (p - ((t*ρ:ℝ):ℂ) * Complex.I - p).im = -(t*ρ) from by
      simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]]
    rw [Complex.neg_re, Complex.ofReal_re]
    field_simp
  · rw [sim_im hρ]
    rw [show (p - ((t*ρ:ℝ):ℂ) * Complex.I - p).re = 0 from by
      simp [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]]
    simp

/-! ## Restricting a map on `ℝ` to the unit interval -/

private def bRes (B : ℝ → ℂ) (hcont : ContinuousOn B (Set.Icc (0:ℝ) 1)) :
    C(Set.Icc (0:ℝ) 1, ℂ) := ⟨Set.domRestrict (Set.Icc (0:ℝ) 1) B, hcont.domRestrict⟩

private lemma bRes_apply (B : ℝ → ℂ) (hcont : ContinuousOn B (Set.Icc (0:ℝ) 1))
    (u : Set.Icc (0:ℝ) 1) : bRes B hcont u = B (u:ℝ) := rfl

private lemma range_bRes (B : ℝ → ℂ) (hcont : ContinuousOn B (Set.Icc (0:ℝ) 1)) :
    Set.range (bRes B hcont) = B '' Set.Icc (0:ℝ) 1 := by
  have : (bRes B hcont : Set.Icc (0:ℝ) 1 → ℂ) = B ∘ Subtype.val := rfl
  rw [this, Set.range_comp, Subtype.range_val]

/-! ## The interior separation in the unit disc

This is the heart of the argument. -/

private theorem separation_of_arcs {B : ℝ → ℂ} {v t : ℝ}
    (hcont : ContinuousOn B (Set.Icc (0:ℝ) 1)) (hinj : Set.InjOn B (Set.Icc (0:ℝ) 1))
    (hmem : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 → B u ∈ Metric.ball (0:ℂ) 1)
    (h0 : B 0 ∈ Metric.sphere (0:ℂ) 1) (h1 : B 1 ∈ Metric.sphere (0:ℂ) 1)
    (hv0 : 0 < v) (hv1 : v < 1) (hv : B v = 0)
    (hax : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (B u).im ≠ 0)
    (hB0im : 0 < (B 0).im) (hB1im : (B 1).im < 0)
    (Bc : C(Set.Icc (0:ℝ) 1, ℂ)) (hBcapp : ∀ u : Set.Icc (0:ℝ) 1, Bc u = B (u:ℝ))
    (hBcinj : Function.Injective Bc)
    (hBcrange : Set.range Bc = B '' Set.Icc (0:ℝ) 1)
    {α α' : C(Set.Icc (0:ℝ) 1, ℂ)}
    (hαinj : Function.Injective α) (hα'inj : Function.Injective α')
    (hαs : ∀ u : Set.Icc (0:ℝ) 1, α u ∈ Metric.sphere (0:ℂ) 1)
    (hα's : ∀ u : Set.Icc (0:ℝ) 1, α' u ∈ Metric.sphere (0:ℂ) 1)
    (hα0 : α 0 = B 0) (hα1 : α 1 = B 1) (hα'0 : α' 0 = B 0) (hα'1 : α' 1 = B 1)
    (hcover : Set.range α ∪ Set.range α' = Metric.sphere (0:ℂ) 1)
    (hdisj : ∀ s t : Set.Icc (0:ℝ) 1, α s = α' t → s = 0 ∨ s = 1)
    (h1mem : (1:ℂ) ∈ Set.range α) (hm1not : (-1:ℂ) ∉ Set.range α)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ¬ JoinedIn (Metric.ball (0:ℂ) 1 \ B '' Set.Icc (0:ℝ) 1) (t : ℂ) (-(t : ℂ)) := by
  classical
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hBc0 : Bc 0 = B 0 := by rw [hBcapp 0]; rfl
  have hBc1 : Bc 1 = B 1 := by rw [hBcapp 1]; rfl
  -- ## the crosscut `β` meets the unit circle only at its endpoints
  have hdisjβ : ∀ s u : Set.Icc (0:ℝ) 1, Bc s = α u → s = 0 ∨ s = 1 := by
    intro s u hst
    have hsph : B (s:ℝ) ∈ Metric.sphere (0:ℂ) 1 := by
      have : Bc s ∈ Metric.sphere (0:ℂ) 1 := hst ▸ hαs u
      rwa [hBcapp s] at this
    by_cases hs0 : s = 0
    · exact Or.inl hs0
    · by_cases hs1 : s = 1
      · exact Or.inr hs1
      · exfalso
        have hb := hmem (s:ℝ) s.2 (fun hh => hs0 (Subtype.ext (by simpa using hh)))
          (fun hh => hs1 (Subtype.ext (by simpa using hh)))
        have hh1 : ‖B (s:ℝ)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hsph
        have hh2 : ‖B (s:ℝ)‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hb
        linarith
  have hB0ne1 : B 0 ≠ B 1 := by
    intro hh
    have := hinj ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, le_refl 1⟩ hh
    exact absurd this (by norm_num)
  -- ## the Jordan curve `C = range Bc ∪ range α`
  have hC : Work.Top.IsJordanCurve (Set.range Bc ∪ Set.range α) :=
    Work.TopJordan.isJordanCurve_of_two_arcs Bc α hBcinj hαinj
      (by rw [hBc0, hα0]) (by rw [hBc1, hα1])
      (by rw [hBc0, hBc1]; exact hB0ne1) hdisjβ
  let S : Work.Top.Sides (Set.range Bc ∪ Set.range α) := Work.TopJordan.sidesOf hC
  have hCsub : (Set.range Bc ∪ Set.range α) ⊆ Metric.closedBall (0:ℂ) 1 := by
    rintro z (hz | hz)
    · obtain ⟨u, rfl⟩ := hz
      rw [hBcapp u]
      by_cases h0u : u = 0
      · have : (u:ℝ) = 0 := congrArg Subtype.val h0u
        rw [this]; exact Metric.sphere_subset_closedBall h0
      · by_cases h1u : u = 1
        · have : (u:ℝ) = 1 := congrArg Subtype.val h1u
          rw [this]; exact Metric.sphere_subset_closedBall h1
        · exact Metric.ball_subset_closedBall
            (hmem (u:ℝ) u.2 (fun hh => h0u (Subtype.ext (by simpa using hh)))
              (fun hh => h1u (Subtype.ext (by simpa using hh))))
    · obtain ⟨u, rfl⟩ := hz
      exact Metric.sphere_subset_closedBall (hαs u)
  -- ## `1` is on the curve, `-1` is not
  have h1sph : (1:ℂ) ∈ Metric.sphere (0:ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]; norm_num
  have h1notBc : (1:ℂ) ∉ Set.range Bc := by
    rintro ⟨u, hu⟩
    have hBu : B (u:ℝ) = 1 := by rw [← hBcapp u]; exact hu
    have hsph : B (u:ℝ) ∈ Metric.sphere (0:ℂ) 1 := by rw [hBu]; exact h1sph
    have key : u = 0 ∨ u = 1 := by
      by_cases h0u : u = 0
      · exact Or.inl h0u
      · by_cases h1u : u = 1
        · exact Or.inr h1u
        · exfalso
          have hb := hmem (u:ℝ) u.2 (fun hh => h0u (Subtype.ext (by simpa using hh)))
            (fun hh => h1u (Subtype.ext (by simpa using hh)))
          have hh1 : ‖B (u:ℝ)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hsph
          have hh2 : ‖B (u:ℝ)‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hb
          linarith
    rcases key with h | h
    · have h' : B 0 = (1:ℂ) := by
        have : (u:ℝ) = 0 := congrArg Subtype.val h
        rw [← this]; exact hBu
      have him : (B 0).im = 0 := by simpa using congrArg Complex.im h'
      linarith [hB0im, him]
    · have h' : B 1 = (1:ℂ) := by
        have : (u:ℝ) = 1 := congrArg Subtype.val h
        rw [← this]; exact hBu
      have him : (B 1).im = 0 := by simpa using congrArg Complex.im h'
      linarith [hB1im, him]
  have h1notα' : (1:ℂ) ∉ Set.range α' := by
    rintro ⟨u, hu⟩
    obtain ⟨s, hs⟩ := h1mem
    have hst : α s = α' u := by rw [hs, hu]
    rcases hdisj s u hst with h | h
    · have h' : (1:ℂ) = B 0 := by rw [← hs, h, hα0]
      have him : (1:ℂ).im = (B 0).im := congrArg Complex.im h'
      simp at him; linarith [hB0im, him]
    · have h' : (1:ℂ) = B 1 := by rw [← hs, h, hα1]
      have him : (1:ℂ).im = (B 1).im := congrArg Complex.im h'
      simp at him; linarith [hB1im, him]
  -- ## local agreement of `C` with the unit circle near `1`
  have hclosed : IsClosed (Set.range Bc ∪ Set.range α') :=
    ((isCompact_range Bc.continuous).union (isCompact_range α'.continuous)).isClosed
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl (1:ℂ) (by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨h1notBc, h1notα'⟩)
  have hδsub' : ∀ z : ℂ, z ∈ Metric.ball (1:ℂ) δ → z ∉ Set.range Bc ∧ z ∉ Set.range α' := by
    intro z hz
    have := hδsub hz
    rwa [Set.mem_compl_iff, Set.mem_union, not_or] at this
  have hδeq : Metric.ball (1:ℂ) δ ∩ Metric.sphere (0:ℂ) 1
      = Metric.ball (1:ℂ) δ ∩ (Set.range Bc ∪ Set.range α) := by
    ext z; constructor
    · rintro ⟨hz1, hz2⟩
      have hzs : z ∈ Set.range α ∪ Set.range α' := hcover.symm ▸ hz2
      refine ⟨hz1, ?_⟩
      rcases hzs with h | h
      · exact Or.inr h
      · exact absurd h (hδsub' z hz1).2
    · rintro ⟨hz1, hz2⟩
      refine ⟨hz1, ?_⟩
      rcases hz2 with h | h
      · exact absurd h (hδsub' z hz1).1
      · obtain ⟨u, rfl⟩ := h
        exact hαs u
  obtain ⟨ε, hεpos, hcap⟩ :=
    Work.Topology.disc_cap_subset_boundedSide S hCsub h1sph ⟨δ, hδpos, hδeq⟩
  -- ## a point of the cap, and the points `±t`
  set η : ℝ := min ε (1 - t) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact div_pos (lt_min hεpos (by linarith)) (by norm_num)
  have hηlt : η < ε := by
    rw [hηdef]
    have h1 : min ε (1 - t) ≤ ε := min_le_left _ _
    linarith
  set s₀ : ℝ := 1 - η with hs₀def
  have hs₀_lt1 : s₀ < 1 := by rw [hs₀def]; linarith
  have hs₀_gt_t : t < s₀ := by
    rw [hs₀def]
    have : η ≤ (1 - t) / 2 := by rw [hηdef]; linarith [min_le_right ε (1 - t)]
    linarith
  have hs₀_pos : 0 < s₀ := lt_trans ht0 hs₀_gt_t
  have hds : dist (s₀ : ℂ) 1 = |s₀ - 1| := by
    rw [dist_eq_norm]
    rw [show (s₀:ℂ) - 1 = ((s₀ - 1 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hs₀m1 : s₀ - 1 < 0 := by linarith
  have hdst : dist (s₀ : ℂ) 1 = η := by
    rw [hds, abs_of_neg hs₀m1, show -(s₀ - 1) = η by rw [hs₀def]; ring]
  have hs₀ball1 : (s₀ : ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs₀_pos]
    exact hs₀_lt1
  have hs₀ball2 : (s₀ : ℂ) ∈ Metric.ball (1:ℂ) ε := by
    rw [Metric.mem_ball, hdst]; exact hηlt
  have hs₀I : (s₀ : ℂ) ∈ S.I := hcap ⟨hs₀ball2, hs₀ball1⟩
  -- ## `t` lies on the same side as the cap
  have hTpre : IsPreconnected ((fun s : ℝ => (s:ℂ)) '' Set.Icc t s₀) :=
    IsPreconnected.image isPreconnected_Icc _ (by fun_prop)
  have hTsub : ((fun s : ℝ => (s:ℂ)) '' Set.Icc t s₀)
      ⊆ (Set.range Bc ∪ Set.range α)ᶜ := by
    rintro z ⟨s, hs, rfl⟩
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · rintro ⟨u, hu⟩
      have hBu : B (u:ℝ) = (s:ℂ) := by rw [← hBcapp u]; exact hu
      have him : (B (u:ℝ)).im = 0 := by rw [hBu]; simp
      have huv : (u:ℝ) = v := by
        by_contra hne
        exact (hax (u:ℝ) u.2 hne) him
      have hszero : (s:ℂ) = 0 := by rw [← hBu, huv]; exact hv
      have hs0 : s = 0 := by have := congrArg Complex.re hszero; simpa using this
      linarith [hs.1, ht0, hs0]
    · rintro ⟨u, hu⟩
      have hnorm : ‖((s:ℝ):ℂ)‖ = 1 := by
        have h1c : ((s:ℝ):ℂ) ∈ Metric.sphere (0:ℂ) 1 := by simpa [hu] using hαs u
        simpa [Metric.mem_sphere, dist_zero_right] using h1c
      have hspos : 0 < s := lt_of_lt_of_le ht0 hs.1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos] at hnorm
      linarith [hnorm, hs.2, hs₀_lt1]
  have htI : (t:ℂ) ∈ S.I := by
    have hTI : ((fun s : ℝ => (s:ℂ)) '' Set.Icc t s₀) ⊆ S.I := by
      rcases S.subset_of_preconnected hTpre hTsub with h | h
      · exact h
      · exact absurd (h ⟨s₀, ⟨hs₀_gt_t.le, le_refl s₀⟩, rfl⟩) (S.notMem_O_of_mem_I hs₀I)
    exact hTI ⟨t, ⟨le_refl t, hs₀_gt_t.le⟩, rfl⟩
  -- ## `-t` lies on the unbounded side
  have hT'pre : IsPreconnected ((fun s : ℝ => (s:ℂ)) '' Set.Iic (-t)) :=
    IsPreconnected.image isPreconnected_Iic _ (by fun_prop)
  have hT'sub : ((fun s : ℝ => (s:ℂ)) '' Set.Iic (-t))
      ⊆ (Set.range Bc ∪ Set.range α)ᶜ := by
    rintro z ⟨s, hs, rfl⟩
    simp only [Set.mem_Iic] at hs
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · rintro ⟨u, hu⟩
      have hBu : B (u:ℝ) = (s:ℂ) := by rw [← hBcapp u]; exact hu
      have him : (B (u:ℝ)).im = 0 := by rw [hBu]; simp
      have huv : (u:ℝ) = v := by
        by_contra hne
        exact (hax (u:ℝ) u.2 hne) him
      have hszero : (s:ℂ) = 0 := by rw [← hBu, huv]; exact hv
      have hs0 : s = 0 := by have := congrArg Complex.re hszero; simpa using this
      linarith [hs, ht0, hs0]
    · rintro ⟨u, hu⟩
      have hnorm : ‖((s:ℝ):ℂ)‖ = 1 := by
        have h1c : ((s:ℝ):ℂ) ∈ Metric.sphere (0:ℂ) 1 := by simpa [hu] using hαs u
        simpa [Metric.mem_sphere, dist_zero_right] using h1c
      rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
      have hsneg : s < 0 := by linarith
      rw [abs_of_neg hsneg] at hnorm
      have hs1 : (fun r : ℝ => (r:ℂ)) s = (-1:ℂ) := by
        show ((s:ℝ):ℂ) = (-1:ℂ)
        have : s = -1 := by linarith
        rw [this]; norm_num
      exact hm1not ⟨u, hu.trans hs1⟩
  have hT'unb : ∀ n : ℕ, ∃ z ∈ ((fun s : ℝ => (s:ℂ)) '' Set.Iic (-t)), (n:ℝ) ≤ ‖z‖ := by
    intro n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    refine ⟨((-((n:ℝ)+1) : ℝ) : ℂ), ⟨-((n:ℝ)+1), ?_, rfl⟩, ?_⟩
    · show -((n:ℝ)+1) ≤ -t
      linarith [le_of_lt ht1, hn]
    · have hneg : (-((n:ℝ)+1) : ℝ) < 0 := by linarith
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
      linarith
  have hmT_O : (-(t:ℂ)) ∈ S.O := by
    have := S.subset_O_of_unbounded hT'pre hT'sub hT'unb
    exact this ⟨-t, le_refl (-t), by simp⟩
  -- ## conclusion
  intro hjoin
  refine S.not_joinedIn htI hmT_O (hjoin.mono ?_)
  rintro z ⟨hz1, hz2⟩
  rw [Set.mem_compl_iff, Set.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · rw [hBcrange]; exact hz2
  · rintro ⟨u, hu⟩
    have hsp : z ∈ Metric.sphere (0:ℂ) 1 := hu ▸ hαs u
    have h1' : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hsp
    have h2' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz1
    linarith

/-! ## The sign of the imaginary part of `B` at the endpoints -/

private theorem unit_crosscut_interior_separation {B : ℝ → ℂ} {v t : ℝ}
    (hcont : ContinuousOn B (Set.Icc (0:ℝ) 1)) (hinj : Set.InjOn B (Set.Icc (0:ℝ) 1))
    (hmem : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 → B u ∈ Metric.ball (0:ℂ) 1)
    (h0 : B 0 ∈ Metric.sphere (0:ℂ) 1) (h1 : B 1 ∈ Metric.sphere (0:ℂ) 1)
    (hv0 : 0 < v) (hv1 : v < 1) (hv : B v = 0)
    (hax : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (B u).im ≠ 0)
    (hsign : (∀ u ∈ Set.Ioo (0:ℝ) v, 0 < (B u).im) ∧ (∀ u ∈ Set.Ioo v 1, (B u).im < 0))
    (ht0 : 0 < t) (ht1 : t < 1) :
    ¬ JoinedIn (Metric.ball (0:ℂ) 1 \ B '' Set.Icc (0:ℝ) 1) (t:ℂ) (-(t:ℂ)) := by
  have hsubL : Set.Icc (0:ℝ) v ⊆ Set.Icc (0:ℝ) 1 := fun x hx => ⟨hx.1, le_trans hx.2 hv1.le⟩
  have hcL : ContinuousOn (fun x : ℝ => (B x).im) (Set.Icc (0:ℝ) v) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsubL)
  have hB0im : 0 < (B 0).im := by
    have h2 : 0 ≤ (B 0).im := nonneg_of_Ioo_pos hv0 hcL hsign.1
    have hne : (B 0).im ≠ 0 := hax 0 ⟨le_refl 0, by norm_num⟩ (ne_of_lt hv0)
    exact lt_of_le_of_ne h2 (Ne.symm hne)
  have hsubR : Set.Icc v 1 ⊆ Set.Icc (0:ℝ) 1 := fun x hx => ⟨le_trans hv0.le hx.1, hx.2⟩
  have hcR : ContinuousOn (fun x : ℝ => (B x).im) (Set.Icc v 1) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono hsubR)
  have hB1im : (B 1).im < 0 := by
    have h2 : (B 1).im ≤ 0 := nonpos_of_Ioo_neg hv1 hcR hsign.2
    have hne : (B 1).im ≠ 0 := hax 1 ⟨by norm_num, le_refl 1⟩ (ne_of_gt hv1)
    exact lt_of_le_of_ne h2 hne
  have hne : B 0 ≠ B 1 := by
    intro hh
    have := hinj ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, le_refl 1⟩ hh
    exact absurd this (by norm_num)
  obtain ⟨α₁, α₂, hα₁inj, hα₂inj, hα₁s, hα₂s, hα₁0, hα₁1, hα₂0, hα₂1, hcover, hdisj,
      harcmem⟩ :=
    Work.Topology.sphere_arcs_of_opposite_halfplanes h0 h1 hne (Or.inl ⟨hB0im, hB1im⟩)
  rcases harcmem with ⟨hm1a, h1b⟩ | ⟨h1a, hm1b⟩
  · -- `-1 ∈ α₁`, `1 ∈ α₂`
    have hdisj' : ∀ s u : Set.Icc (0:ℝ) 1, α₂ s = α₁ u → s = 0 ∨ s = 1 := by
      intro s u hsu
      rcases hdisj u s hsu.symm with h | h
      · left; apply hα₂inj; rw [hsu, h, hα₁0, hα₂0]
      · right; apply hα₂inj; rw [hsu, h, hα₁1, hα₂1]
    have hm1not : (-1:ℂ) ∉ Set.range α₂ := by
      rintro ⟨s, hs⟩
      obtain ⟨u, hu⟩ := hm1a
      rcases hdisj' s u (by rw [hs, hu]) with h | h
      · have h' : (-1:ℂ) = B 0 := by rw [← hs, h, hα₂0]
        have him : (-1:ℂ).im = (B 0).im := congrArg Complex.im h'
        simp at him; linarith [hB0im, him]
      · have h' : (-1:ℂ) = B 1 := by rw [← hs, h, hα₂1]
        have him : (-1:ℂ).im = (B 1).im := congrArg Complex.im h'
        simp at him; linarith [hB1im, him]
    exact separation_of_arcs hcont hinj hmem h0 h1 hv0 hv1 hv hax hB0im hB1im
      (bRes B hcont) (bRes_apply B hcont) (fun a b hab => Subtype.ext (hinj a.2 b.2 (by
        rw [bRes_apply B hcont a, bRes_apply B hcont b] at hab; exact hab)))
      (range_bRes B hcont) hα₂inj hα₁inj hα₂s hα₁s hα₂0 hα₂1 hα₁0 hα₁1
      (by rw [Set.union_comm]; exact hcover) hdisj' h1b hm1not ht0 ht1
  · -- `1 ∈ α₁`, `-1 ∈ α₂`
    have hm1not : (-1:ℂ) ∉ Set.range α₁ := by
      rintro ⟨s, hs⟩
      obtain ⟨u, hu⟩ := hm1b
      rcases hdisj s u (by rw [hs, hu]) with h | h
      · have h' : (-1:ℂ) = B 0 := by rw [← hs, h, hα₁0]
        have him : (-1:ℂ).im = (B 0).im := congrArg Complex.im h'
        simp at him; linarith [hB0im, him]
      · have h' : (-1:ℂ) = B 1 := by rw [← hs, h, hα₁1]
        have him : (-1:ℂ).im = (B 1).im := congrArg Complex.im h'
        simp at him; linarith [hB1im, him]
    exact separation_of_arcs hcont hinj hmem h0 h1 hv0 hv1 hv hax hB0im hB1im
      (bRes B hcont) (bRes_apply B hcont) (fun a b hab => Subtype.ext (hinj a.2 b.2 (by
        rw [bRes_apply B hcont a, bRes_apply B hcont b] at hab; exact hab)))
      (range_bRes B hcont) hα₁inj hα₂inj hα₁s hα₂s hα₁0 hα₁1 hα₂0 hα₂1
      hcover hdisj h1a hm1not ht0 ht1

/-! ## The main theorem -/

theorem crosscut_separation_ball {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ → ℂ} {v : ℝ}
    (hcont : ContinuousOn β (Set.Icc (0:ℝ) 1))
    (hinj : Set.InjOn β (Set.Icc (0:ℝ) 1))
    (h0 : β 0 ∈ Metric.sphere p ρ) (h1 : β 1 ∈ Metric.sphere p ρ)
    (hint : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 → β u ∈ Metric.ball p ρ)
    (hv0 : 0 < v) (hv1 : v < 1) (hv : β v = p)
    (hax : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (β u).re ≠ p.re)
    (hsign : (∀ u ∈ Set.Ioo (0:ℝ) v, (β u).re < p.re) ∧
             (∀ u ∈ Set.Ioo v 1, p.re < (β u).re)) :
    ∀ t : ℝ, 0 < t → t < 1 →
      ¬ JoinedIn (Metric.ball p ρ \ β '' Set.Icc (0:ℝ) 1)
        (p + (t * ρ) * Complex.I) (p - (t * ρ) * Complex.I) := by
  intro t ht0 ht1 hjoin
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hBcont : ContinuousOn (fun u => sim p ρ (β u)) (Set.Icc (0:ℝ) 1) :=
    (sim_cont p ρ).comp_continuousOn hcont
  have hBinj : Set.InjOn (fun u => sim p ρ (β u)) (Set.Icc (0:ℝ) 1) :=
    fun a ha b hb hab => hinj ha hb (sim_injective hρ hab)
  have hBmem : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ 0 → u ≠ 1 →
      sim p ρ (β u) ∈ Metric.ball (0:ℂ) 1 :=
    fun u hu hu0 hu1 => (sim_mem_ball hρ (β u)).mpr (hint u hu hu0 hu1)
  have hB0 : sim p ρ (β 0) ∈ Metric.sphere (0:ℂ) 1 := (sim_mem_sphere hρ (β 0)).mpr h0
  have hB1 : sim p ρ (β 1) ∈ Metric.sphere (0:ℂ) 1 := (sim_mem_sphere hρ (β 1)).mpr h1
  have hBv : sim p ρ (β v) = 0 := by rw [hv]; exact sim_p hρne
  have hBax : ∀ u ∈ Set.Icc (0:ℝ) 1, u ≠ v → (sim p ρ (β u)).im ≠ 0 := by
    intro u hu huv h0'
    have := (sim_im_eq_zero hρne (β u)).mp h0'
    exact hax u hu huv this
  have hBsign : (∀ u ∈ Set.Ioo (0:ℝ) v, 0 < (sim p ρ (β u)).im) ∧
      (∀ u ∈ Set.Ioo v 1, (sim p ρ (β u)).im < 0) := by
    constructor
    · intro u hu
      rw [sim_im hρne]
      apply div_pos
      · simp only [Complex.sub_re]; linarith [hsign.1 u hu]
      · exact hρ
    · intro u hu
      rw [sim_im hρne]
      apply div_neg_of_neg_of_pos
      · simp only [Complex.sub_re]; linarith [hsign.2 u hu]
      · exact hρ
  have hkey := unit_crosscut_interior_separation (B := fun u => sim p ρ (β u))
    hBcont hBinj hBmem hB0 hB1 hv0 hv1 hBv hBax hBsign ht0 ht1
  -- build the corresponding path in the unit disc
  have hjoinUnit : JoinedIn (Metric.ball (0:ℂ) 1 \ (fun u => sim p ρ (β u)) '' Set.Icc (0:ℝ) 1)
      (t:ℂ) (-(t:ℂ)) := by
    refine ⟨Path.mk ⟨fun s => sim p ρ (hjoin.somePath s),
        (sim_cont p ρ).comp hjoin.somePath.continuous⟩ ?_ ?_, ?_⟩
    · show sim p ρ (hjoin.somePath 0) = (t:ℂ)
      rw [Path.source hjoin.somePath]
      exact sim_pt hρne
    · show sim p ρ (hjoin.somePath 1) = -(t:ℂ)
      rw [Path.target hjoin.somePath]
      exact sim_mt hρne
    · intro s
      have hγs := hjoin.somePath_mem s
      simp only [Set.mem_sdiff] at hγs
      obtain ⟨hball, hnotimg⟩ := hγs
      show sim p ρ (hjoin.somePath s)
        ∈ Metric.ball (0:ℂ) 1 \ (fun u => sim p ρ (β u)) '' Set.Icc (0:ℝ) 1
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, sim_norm hρ]
        rw [Metric.mem_ball, dist_eq_norm] at hball
        rw [div_lt_one hρ]
        rw [dist_eq_norm]
        exact hball
      · rintro ⟨u, hu, hBu⟩
        have hEq : hjoin.somePath s = β u := sim_injective hρ hBu.symm
        exact hnotimg ⟨u, hu, hEq.symm⟩
  exact hkey hjoinUnit

end

end Work.ELRig
