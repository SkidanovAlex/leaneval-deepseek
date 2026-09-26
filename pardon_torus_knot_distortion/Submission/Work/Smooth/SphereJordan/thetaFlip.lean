import Mathlib
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.SphereJordan.planeThetaCurves
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.SphereJordan.incrOn

/-!
# The winding numbers of the four theta-graph curves: the "flip" relations

For a plane theta configuration `T : ThetaSetup D₁ D₂` and booleans `i j`, `T.cur i j` is the
four-arc simple closed curve `arcA i · α · arcB j · β̄`.  This module proves that swapping the
`D₁`-boundary arc changes the winding number about a point `x` off both curves by the winding
number of the whole boundary circle `∂D₁ = discCurve T.f` about `x` (and dually for `D₂`).

The proof uses the *argument increment* `Work.SphereJordan.incOn` (module `argIncrement`): the loop
`(T.cur i j).γ` on `[0, 2π]` consists of the four pieces `arcA i`, `α`, `arcB j`, `β̄`, so
`incOn` over a full period splits (`incOn_add`) into the four corresponding increments; the three
pieces other than `arcA i` are *identical* for `i = true` and `i = false`, so they cancel in the
difference.  The difference of the two `arcA`-increments is  `incOn` of the two arcs of `∂D₁`,
which by `incOn_rev` and `incOn_add` is `incOn` over `[θp - 2π, θp]`, i.e. `windNumber * 2πI`
(`incOn_period`).  `incOn_windNumber` converts back.

The pointwise descriptions of the four pieces (`loopC_quarter`, `loopC_alpha`, `loopC_arcB`) are
copied from `Submission/Work/Smooth/SphereJordan/thetaWinding.lean` (which cannot be imported here
because of an import cycle); they are placed in the fresh namespace
`Work.Smooth.SphereJordan.ThetaFlip` so that no name clashes with the original arise.
-/

open Set
open Work.Smooth.SphereJordan
open Work.Smooth.SphereJordan.ThetaSetup

namespace Work.Smooth.SphereJordan.ThetaFlip

noncomputable section

variable {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂)

theorem loopC_quarter (i j : Bool) {t : Set.Icc (0:ℝ) 1} (ht : (t:ℝ) ≤ 1/4) :
    T.loopC i j t = T.arcA i ⟨4*(t:ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  rw [loopC, loopP, Path.trans_apply]
  rw [dif_pos (show (t:ℝ) ≤ 1/2 by linarith [t.2.1])]
  rw [halfP, Path.trans_apply]
  rw [dif_pos (show 2*(t:ℝ) ≤ 1/2 by linarith)]
  change T.arcA i (⟨2 * (2 * (t:ℝ)), _⟩ : Set.Icc (0:ℝ) 1)
    = T.arcA i ⟨4*(t:ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩
  congr 1
  apply Subtype.ext
  ring

/-- **The piece of the loop between the first quarter and three eighths is the joining arc
`α`.** -/
theorem loopC_alpha (i j : Bool) {t : Set.Icc (0:ℝ) 1} (h1 : 1/4 < (t:ℝ))
    (h2 : (t:ℝ) ≤ 3/8) :
    T.loopC i j t = T.α ⟨8*(t:ℝ) - 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  rw [loopC, loopP, Path.trans_apply, dif_pos (by linarith)]
  rw [halfP, Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
  rw [Path.trans_apply, dif_pos (by simp only [Subtype.coe_mk]; linarith)]
  change T.α (⟨2 * (2 * (2 * (t:ℝ)) - 1), _⟩ : Set.Icc (0:ℝ) 1)
    = T.α ⟨8*(t:ℝ) - 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  congr 1
  apply Subtype.ext
  ring

/-- **The piece of the loop between three eighths and one half is the boundary arc `arcB j`.** -/
theorem loopC_arcB (i j : Bool) {t : Set.Icc (0:ℝ) 1} (h1 : 3/8 ≤ (t:ℝ)) (h2 : (t:ℝ) ≤ 1/2) :
    T.loopC i j t = T.arcB j ⟨8*(t:ℝ) - 3, by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  by_cases hlt : (3/8 : ℝ) < (t:ℝ)
  · rw [loopC, loopP, Path.trans_apply, dif_pos (by linarith)]
    rw [halfP, Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
    rw [Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
    change T.arcB j (⟨2 * (2 * (2 * (t:ℝ)) - 1) - 1, _⟩ : Set.Icc (0:ℝ) 1)
      = T.arcB j ⟨8*(t:ℝ) - 3, by constructor <;> linarith [t.2.1, t.2.2]⟩
    congr 1
    apply Subtype.ext
    ring
  · have ht : (t:ℝ) = 3/8 := le_antisymm (le_of_not_gt hlt) h1
    rw [loopC, loopP, Path.trans_apply, dif_pos (by linarith)]
    rw [halfP, Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
    rw [Path.trans_apply, dif_pos (by simp only [Subtype.coe_mk]; linarith)]
    rw [show (⟨2 * (2 * (2 * (t:ℝ)) - 1),
          by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0:ℝ) 1) = ⟨1, by norm_num⟩
        from Subtype.ext (by simp only [Subtype.coe_mk]; linarith),
      show (⟨8 * (t:ℝ) - 3, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0:ℝ) 1)
          = ⟨0, by norm_num⟩
        from Subtype.ext (by simp only [Subtype.coe_mk]; linarith),
      T.arcB_zero j]
    rfl



/-- **The loop is independent of `i` after the first quarter.** -/
theorem loopC_eq_of_quarter_le (j : Bool) {t : Set.Icc (0:ℝ) 1} (ht : 1/4 ≤ (t:ℝ)) :
    T.loopC true j t = T.loopC false j t := by
  by_cases h : (t:ℝ) ≤ 1/4
  · rw [loopC_quarter T true j h, loopC_quarter T false j h]
    rw [show (⟨4*(t:ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0:ℝ) 1)
        = ⟨1, by norm_num⟩ from Subtype.ext (by simp only [Subtype.coe_mk]; linarith)]
    rw [T.arcA_one true, T.arcA_one false]
  · by_cases h2 : (t:ℝ) ≤ 3/8
    · rw [loopC_alpha T true j (not_le.mp h) h2, loopC_alpha T false j (not_le.mp h) h2]
    · by_cases h3 : (t:ℝ) ≤ 1/2
      · rw [loopC_arcB (t := t) T true j (le_of_lt (not_le.mp h2)) h3,
          loopC_arcB (t := t) T false j (le_of_lt (not_le.mp h2)) h3]
      · rw [loopC, loopP, Path.trans_apply, dif_neg h3]
        rw [loopC, loopP, Path.trans_apply, dif_neg h3]

/-- **The loop is independent of `j` up to three eighths.** -/
theorem loopC_eq_of_le_threeEighth (i : Bool) {t : Set.Icc (0:ℝ) 1} (ht : (t:ℝ) ≤ 3/8) :
    T.loopC i true t = T.loopC i false t := by
  by_cases h : (t:ℝ) ≤ 1/4
  · rw [loopC_quarter T i true h, loopC_quarter T i false h]
  · rw [loopC_alpha T i true (not_le.mp h) ht, loopC_alpha T i false (not_le.mp h) ht]



/-- A point of the boundary circle is not an interior point. -/
theorem circlePoint_ne_of_norm_lt {z : Disc} (hz : ‖(z : ℂ)‖ < 1) (τ : ℝ) :
    T.f (circlePoint τ) ≠ T.f z := by
  intro hcon
  have h1 : ((circlePoint τ : Disc) : ℂ) = (z : ℂ) := congrArg (fun w : Disc => (w : ℂ)) (T.hf hcon)
  have h2 : ‖((circlePoint τ : Disc) : ℂ)‖ = ‖(z : ℂ)‖ := congrArg (fun w : ℂ => ‖w‖) h1
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at h2
  linarith

theorem circlePoint_ne_of_norm_lt_g {z : Disc} (hz : ‖(z : ℂ)‖ < 1) (τ : ℝ) :
    T.g (circlePoint τ) ≠ T.g z := by
  intro hcon
  have h1 : ((circlePoint τ : Disc) : ℂ) = (z : ℂ) := congrArg (fun w : Disc => (w : ℂ)) (T.hg hcon)
  have h2 : ‖((circlePoint τ : Disc) : ℂ)‖ = ‖(z : ℂ)‖ := congrArg (fun w : ℂ => ‖w‖) h1
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at h2
  linarith



/-- The interior points of `D₁` avoid the trace of every four-arc curve. -/
theorem f_notMem_cur_trace (z : Disc) (hz : ‖(z : ℂ)‖ < 1) (i j : Bool) :
    T.f z ∉ (T.cur i j).trace := by
  have hfD₁ : T.f z ∈ D₁ := by
    have h : T.f z ∈ Set.range T.f := ⟨z, rfl⟩
    rwa [T.hfr] at h
  have hcirc : ∀ τ : ℝ, T.f (circlePoint τ) ≠ T.f z := circlePoint_ne_of_norm_lt T hz
  rw [T.cur_range i j]
  intro hmem
  simp only [Set.mem_union] at hmem
  rcases hmem with ((h | h) | h) | h
  · obtain ⟨t, ht⟩ := h
    cases i
    · refine hcirc (T.θq + (t:ℝ) * ((T.θp - 2 * Real.pi) - T.θq)) ?_
      rw [← ht, show T.arcA false = discArc T.f T.θq (T.θp - 2 * Real.pi) from rfl, discArc_apply]
    · refine hcirc (T.θq + (t:ℝ) * (T.θp - T.θq)) ?_
      rw [← ht, show T.arcA true = discArc T.f T.θq T.θp from rfl, discArc_apply]
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      refine hcirc T.θp ?_
      rw [← ht, ht0]
      exact T.hθp
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hαint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inl hfD₁)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      have ha : T.a ∈ D₂ := T.hα₁
      exact Set.disjoint_left.mp T.hdisj hfD₁ (by rw [← ht, ht1]; exact ha)
  · obtain ⟨t, ht⟩ := h
    have h1 : T.arcB j t ∈ D₂ := T.range_arcB_subset j ⟨t, rfl⟩
    exact Set.disjoint_left.mp T.hdisj hfD₁ (by rw [← ht]; exact h1)
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      refine hcirc T.θq ?_
      rw [← ht, ht0]
      exact T.hθq
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hβint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inl hfD₁)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      have hb : T.b ∈ D₂ := T.hβ₁
      exact Set.disjoint_left.mp T.hdisj hfD₁ (by rw [← ht, ht1]; exact hb)

/-- The interior points of `D₂` avoid the trace of every four-arc curve. -/
theorem g_notMem_cur_trace (z : Disc) (hz : ‖(z : ℂ)‖ < 1) (i j : Bool) :
    T.g z ∉ (T.cur i j).trace := by
  have hgD₂ : T.g z ∈ D₂ := by
    have h : T.g z ∈ Set.range T.g := ⟨z, rfl⟩
    rwa [T.hgr] at h
  have hcirc : ∀ τ : ℝ, T.g (circlePoint τ) ≠ T.g z := circlePoint_ne_of_norm_lt_g T hz
  rw [T.cur_range i j]
  intro hmem
  simp only [Set.mem_union] at hmem
  rcases hmem with ((h | h) | h) | h
  · obtain ⟨t, ht⟩ := h
    have h1 : T.arcA i t ∈ D₁ := T.range_arcA_subset i ⟨t, rfl⟩
    exact Set.disjoint_left.mp T.hdisj (by rw [← ht]; exact h1) hgD₂
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      have hp : T.p ∈ D₁ := by
        have h : T.f (circlePoint T.θp) ∈ Set.range T.f := ⟨circlePoint T.θp, rfl⟩
        rw [T.hθp] at h
        rwa [T.hfr] at h
      exact Set.disjoint_left.mp T.hdisj (by rw [← ht, ht0]; exact hp) hgD₂
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hαint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inr hgD₂)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      refine hcirc T.φa ?_
      rw [← ht, ht1]
      exact T.hφa
  · obtain ⟨t, ht⟩ := h
    cases j
    · refine hcirc (T.φa + (t:ℝ) * (T.φb - T.φa)) ?_
      rw [← ht, show T.arcB false = discArc T.g T.φa T.φb from rfl, discArc_apply]
    · refine hcirc (T.φa + (t:ℝ) * ((T.φb + 2 * Real.pi) - T.φa)) ?_
      rw [← ht, show T.arcB true = discArc T.g T.φa (T.φb + 2 * Real.pi) from rfl, discArc_apply]
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      have hq : T.q ∈ D₁ := by
        have h : T.f (circlePoint T.θq) ∈ Set.range T.f := ⟨circlePoint T.θq, rfl⟩
        rw [T.hθq] at h
        rwa [T.hfr] at h
      exact Set.disjoint_left.mp T.hdisj (by rw [← ht, ht0]; exact hq) hgD₂
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hβint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inr hgD₂)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      refine hcirc T.φb ?_
      rw [← ht, ht1]
      exact T.hφb

/-- **The centre points of the two discs avoid the trace of every four-arc curve.** -/
theorem center_notMem_cur_trace (z : Disc) (hz : ‖(z : ℂ)‖ < 1) (i j : Bool) :
    T.f z ∉ (T.cur i j).trace ∧ T.g z ∉ (T.cur i j).trace :=
  ⟨f_notMem_cur_trace T z hz i j, g_notMem_cur_trace T z hz i j⟩

/-! ## The four pieces of the four-arc curve -/

/-- At the origin the four-arc curve is at `q`. -/
theorem cur_γ_zero (i j : Bool) : (T.cur i j).γ 0 = T.q := by
  have hs : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl _, Real.two_pi_pos⟩
  calc (T.cur i j).γ 0 = loopFn (T.loopCf i j) 0 :=
        loopCurve_apply_of_Ico (T.loopCf i j) (T.loopC_closed i j) hs
    _ = (T.loopCf i j) ⟨(0:ℝ) / (2 * Real.pi),
          ⟨div_nonneg hs.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hs.2.le⟩⟩ :=
        loopFn_of_mem (T.loopCf i j) ⟨hs.1, hs.2.le⟩
    _ = T.loopC i j (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
        show T.loopC i j ⟨(0:ℝ) / (2 * Real.pi), _⟩ = T.loopC i j (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1)
        congr 1
        apply Subtype.ext
        simp
    _ = T.q := T.loopC_zero i j

/-- `(cur i j).γ` at `2π u` is the loop value `loopC i j u`. -/
theorem cur_γ_eq_loopC (i j : Bool) (u : Set.Icc (0 : ℝ) 1) :
    (T.cur i j).γ (2 * Real.pi * (u : ℝ)) = T.loopC i j u := by
  rcases lt_or_eq_of_le u.2.2 with hlt | heq
  · have hs : 2 * Real.pi * (u : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨mul_nonneg Real.two_pi_pos.le u.2.1, by nlinarith [Real.pi_pos, hlt]⟩
    calc (T.cur i j).γ (2 * Real.pi * (u : ℝ))
        = loopFn (T.loopCf i j) (2 * Real.pi * (u : ℝ)) :=
          loopCurve_apply_of_Ico (T.loopCf i j) (T.loopC_closed i j) hs
      _ = (T.loopCf i j) ⟨2 * Real.pi * (u : ℝ) / (2 * Real.pi),
            ⟨div_nonneg hs.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hs.2.le⟩⟩ :=
          loopFn_of_mem (T.loopCf i j) ⟨hs.1, hs.2.le⟩
      _ = T.loopC i j u := by
          show T.loopC i j ⟨2 * Real.pi * (u : ℝ) / (2 * Real.pi), _⟩ = T.loopC i j u
          congr 1
          apply Subtype.ext
          show 2 * Real.pi * (u : ℝ) / (2 * Real.pi) = (u : ℝ)
          field_simp
  · have hu : u = (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext heq
    rw [hu]
    have h2π : 2 * Real.pi * ((⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ) = 2 * Real.pi := by
      norm_num
    rw [h2π]
    have hper : (T.cur i j).γ (2 * Real.pi) = (T.cur i j).γ 0 := by
      have h := (T.cur i j).periodic 0
      simpa only [zero_add] using h
    have h0 : (T.cur i j).γ 0 = T.q := cur_γ_zero T i j
    exact hper.trans (h0.trans (T.loopC_one i j).symm)

/-- At half a period the curve is at `b`. -/
theorem loopC_half (i j : Bool) :
    T.loopC i j (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) = T.b := by
  have hc : ((⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 := le_refl _
  rw [loopC, loopP, Path.trans_apply, dif_pos hc]
  convert Path.target (T.halfP i j) using 2
  apply Subtype.ext
  norm_num

/-- On the first quarter of its period the curve is the boundary arc `arcA i`. -/
theorem cur_γ_first (i j : Bool) (t : Set.Icc (0 : ℝ) 1) :
    (T.cur i j).γ (Real.pi / 2 * (t : ℝ)) = T.arcA i t := by
  have h0 : (0 : ℝ) ≤ Real.pi / 2 * (t : ℝ) := by nlinarith [Real.pi_pos, t.2.1]
  have hlt : Real.pi / 2 * (t : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos, t.2.2]
  have hs : Real.pi / 2 * (t : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨h0, hlt⟩
  set u : Set.Icc (0 : ℝ) 1 := ⟨Real.pi / 2 * (t : ℝ) / (2 * Real.pi),
    ⟨div_nonneg h0 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hs.2.le⟩⟩ with hu
  have hval : (u : ℝ) = Real.pi / 2 * (t : ℝ) / (2 * Real.pi) := by rw [hu]
  have hbase : (T.cur i j).γ (Real.pi / 2 * (t : ℝ)) = T.loopC i j u := by
    rw [show Real.pi / 2 * (t : ℝ) = 2 * Real.pi * (u : ℝ) from by rw [hval]; field_simp]
    exact cur_γ_eq_loopC T i j u
  rw [hbase]
  have hle : (u : ℝ) ≤ 1 / 4 := by
    rw [hval, div_le_iff₀ Real.two_pi_pos]
    nlinarith [Real.pi_pos, t.2.2]
  rw [loopC_quarter T i j (t := u) hle]
  congr 1
  apply Subtype.ext
  show 4 * (u : ℝ) = (t : ℝ)
  rw [hval]
  field_simp
  ring_nf

/-- On the piece `[3π/4, π]` of its period the curve is the boundary arc `arcB j`. -/
theorem cur_γ_third (i j : Bool) (t : Set.Icc (0 : ℝ) 1) :
    (T.cur i j).γ (3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ)) = T.arcB j t := by
  have h0 : (0 : ℝ) ≤ 3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ) := by
    nlinarith [Real.pi_pos, t.2.1]
  have hlt : 3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_pos, t.2.2]
  have hs : 3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨h0, hlt⟩
  set u : Set.Icc (0 : ℝ) 1 := ⟨(3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ)) / (2 * Real.pi),
    ⟨div_nonneg h0 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hs.2.le⟩⟩ with hu
  have hval : (u : ℝ) = (3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ)) / (2 * Real.pi) := by rw [hu]
  have hbase : (T.cur i j).γ (3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ)) = T.loopC i j u := by
    rw [show 3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ) = 2 * Real.pi * (u : ℝ) from by
      rw [hval]; field_simp]
    exact cur_γ_eq_loopC T i j u
  rw [hbase]
  have hle1 : 3 / 8 ≤ (u : ℝ) := by
    rw [hval, le_div_iff₀ Real.two_pi_pos]
    nlinarith [Real.pi_pos, t.2.1]
  have hle2 : (u : ℝ) ≤ 1 / 2 := by
    rw [hval, div_le_iff₀ Real.two_pi_pos]
    nlinarith [Real.pi_pos, t.2.2]
  rw [loopC_arcB T i j hle1 hle2]
  congr 1
  apply Subtype.ext
  show 8 * (u : ℝ) - 3 = (t : ℝ)
  rw [hval]
  field_simp
  ring_nf

/-- After the first quarter of its period the curve is independent of `i`. -/
theorem cur_γ_eq_of_quarter_le (j : Bool) {s : ℝ} (h1 : Real.pi / 2 ≤ s)
    (h2 : s ≤ 2 * Real.pi) : (T.cur true j).γ s = (T.cur false j).γ s := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_trans (by positivity) h1, hlt⟩
    set u : Set.Icc (0 : ℝ) 1 := ⟨s / (2 * Real.pi),
      ⟨div_nonneg hs.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hs.2.le⟩⟩ with hu
    have hs' : s = 2 * Real.pi * (u : ℝ) := by rw [hu]; field_simp
    have hL := cur_γ_eq_loopC T true j u
    rw [← hs'] at hL
    have hR := cur_γ_eq_loopC T false j u
    rw [← hs'] at hR
    rw [hL, hR]
    refine loopC_eq_of_quarter_le T j ?_
    rw [hu, le_div_iff₀ Real.two_pi_pos]
    nlinarith [Real.pi_pos, h1]
  · have h2π : s = 2 * Real.pi := heq
    rw [h2π]
    have hp : (T.cur true j).γ (2 * Real.pi) = T.q := by
      rw [show (T.cur true j).γ (2 * Real.pi) = (T.cur true j).γ 0 from by
        have h := (T.cur true j).periodic 0
        simpa only [zero_add] using h, cur_γ_zero T true j]
    have hq : (T.cur false j).γ (2 * Real.pi) = T.q := by
      rw [show (T.cur false j).γ (2 * Real.pi) = (T.cur false j).γ 0 from by
        have h := (T.cur false j).periodic 0
        simpa only [zero_add] using h, cur_γ_zero T false j]
    rw [hp, hq]

/-- Before three eighths of its period the curve is independent of `j`. -/
theorem cur_γ_eq_of_le_threeEighth (i : Bool) {s : ℝ} (h0 : 0 ≤ s)
    (h2 : s ≤ 3 * Real.pi / 4) : (T.cur i true).γ s = (T.cur i false).γ s := by
  have hlt : s < 2 * Real.pi := by nlinarith [Real.pi_pos, h2]
  set u : Set.Icc (0 : ℝ) 1 := ⟨s / (2 * Real.pi),
    ⟨div_nonneg h0 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hlt.le⟩⟩ with hu
  have hs' : s = 2 * Real.pi * (u : ℝ) := by rw [hu]; field_simp
  have hL := cur_γ_eq_loopC T i true u
  rw [← hs'] at hL
  have hR := cur_γ_eq_loopC T i false u
  rw [← hs'] at hR
  rw [hL, hR]
  refine loopC_eq_of_le_threeEighth T i ?_
  rw [hu, div_le_iff₀ Real.two_pi_pos]
  nlinarith [Real.pi_pos, h2]

/-- After half a period the curve is independent of `j` (the reversed arc `β`). -/
theorem cur_γ_eq_of_pi_le (i : Bool) {s : ℝ} (h1 : Real.pi ≤ s) (h2 : s ≤ 2 * Real.pi) :
    (T.cur i true).γ s = (T.cur i false).γ s := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_trans (by positivity) h1, hlt⟩
    set u : Set.Icc (0 : ℝ) 1 := ⟨s / (2 * Real.pi),
      ⟨div_nonneg hs.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hs.2.le⟩⟩ with hu
    have hs' : s = 2 * Real.pi * (u : ℝ) := by rw [hu]; field_simp
    have hhalf : 1 / 2 ≤ (u : ℝ) := by
      rw [hu, le_div_iff₀ Real.two_pi_pos]; nlinarith [Real.pi_pos, h1]
    have hL := cur_γ_eq_loopC T i true u
    rw [← hs'] at hL
    have hR := cur_γ_eq_loopC T i false u
    rw [← hs'] at hR
    rw [hL, hR]
    rcases lt_or_eq_of_le hhalf with hlt2 | heq2
    · rw [loopC, loopP, Path.trans_apply, dif_neg (by rw [not_le]; exact hlt2)]
      rw [loopC, loopP, Path.trans_apply, dif_neg (by rw [not_le]; exact hlt2)]
    · have hu' : u = (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext heq2.symm
      rw [hu']
      exact (loopC_half T i true).trans (loopC_half T i false).symm
  · have h2π : s = 2 * Real.pi := heq
    rw [h2π]
    have hp : (T.cur i true).γ (2 * Real.pi) = T.q := by
      rw [show (T.cur i true).γ (2 * Real.pi) = (T.cur i true).γ 0 from by
        have h := (T.cur i true).periodic 0
        simpa only [zero_add] using h, cur_γ_zero T i true]
    have hq : (T.cur i false).γ (2 * Real.pi) = T.q := by
      rw [show (T.cur i false).γ (2 * Real.pi) = (T.cur i false).γ 0 from by
        have h := (T.cur i false).periodic 0
        simpa only [zero_add] using h, cur_γ_zero T i false]
    rw [hp, hq]

/-! ## The increment identities -/

theorem incOn_cur_first_true (j : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x 0 (Real.pi / 2)
      = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq T.θp := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  show (T.cur true j).γ (0 + (t : ℝ) * (Real.pi / 2 - 0)) - x
      = (discCurve T.f).γ (T.θq + (t : ℝ) * (T.θp - T.θq)) - x
  rw [show (0 : ℝ) + (t : ℝ) * (Real.pi / 2 - 0) = Real.pi / 2 * (t : ℝ) from by ring]
  refine congrArg (fun w : ℂ => w - x) ?_
  rw [cur_γ_first T true j t]
  show T.arcA true t = T.f (Work.Smooth.Jordan.circlePoint (T.θq + (t : ℝ) * (T.θp - T.θq)))
  rw [show T.arcA true = discArc T.f T.θq T.θp from rfl, discArc_apply]

theorem incOn_cur_first_false (j : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x 0 (Real.pi / 2)
      = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq (T.θp - 2 * Real.pi) := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  show (T.cur false j).γ (0 + (t : ℝ) * (Real.pi / 2 - 0)) - x
      = (discCurve T.f).γ (T.θq + (t : ℝ) * ((T.θp - 2 * Real.pi) - T.θq)) - x
  rw [show (0 : ℝ) + (t : ℝ) * (Real.pi / 2 - 0) = Real.pi / 2 * (t : ℝ) from by ring]
  refine congrArg (fun w : ℂ => w - x) ?_
  rw [cur_γ_first T false j t]
  show T.arcA false t = T.f (Work.Smooth.Jordan.circlePoint (T.θq + (t : ℝ) * ((T.θp - 2 * Real.pi) - T.θq)))
  rw [show T.arcA false = discArc T.f T.θq (T.θp - 2 * Real.pi) from rfl, discArc_apply]

theorem incOn_cur_third_true (i : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x (3 * Real.pi / 4) Real.pi
      = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa (T.φb + 2 * Real.pi) := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  show (T.cur i true).γ (3 * Real.pi / 4 + (t : ℝ) * (Real.pi - 3 * Real.pi / 4)) - x
      = (discCurve T.g).γ (T.φa + (t : ℝ) * ((T.φb + 2 * Real.pi) - T.φa)) - x
  rw [show 3 * Real.pi / 4 + (t : ℝ) * (Real.pi - 3 * Real.pi / 4)
      = 3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ) from by ring]
  refine congrArg (fun w : ℂ => w - x) ?_
  rw [cur_γ_third T i true t]
  show T.arcB true t = T.g (Work.Smooth.Jordan.circlePoint (T.φa + (t : ℝ) * ((T.φb + 2 * Real.pi) - T.φa)))
  rw [show T.arcB true = discArc T.g T.φa (T.φb + 2 * Real.pi) from rfl, discArc_apply]

theorem incOn_cur_third_false (i : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x (3 * Real.pi / 4) Real.pi
      = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa T.φb := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  show (T.cur i false).γ (3 * Real.pi / 4 + (t : ℝ) * (Real.pi - 3 * Real.pi / 4)) - x
      = (discCurve T.g).γ (T.φa + (t : ℝ) * (T.φb - T.φa)) - x
  rw [show 3 * Real.pi / 4 + (t : ℝ) * (Real.pi - 3 * Real.pi / 4)
      = 3 * Real.pi / 4 + Real.pi / 4 * (t : ℝ) from by ring]
  refine congrArg (fun w : ℂ => w - x) ?_
  rw [cur_γ_third T i false t]
  show T.arcB false t = T.g (Work.Smooth.Jordan.circlePoint (T.φa + (t : ℝ) * (T.φb - T.φa)))
  rw [show T.arcB false = discArc T.g T.φa T.φb from rfl, discArc_apply]

theorem incOn_cur_agree (j : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x (Real.pi / 2) (2 * Real.pi)
      = Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x (Real.pi / 2)
          (2 * Real.pi) := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  refine congrArg (fun w : ℂ => w - x) ?_
  exact cur_γ_eq_of_quarter_le T j (by nlinarith [t.2.1, Real.pi_pos])
    (by nlinarith [t.2.2, Real.pi_pos])

theorem incOn_cur_agree_low (i : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x 0 (3 * Real.pi / 4)
      = Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x 0 (3 * Real.pi / 4) := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  refine congrArg (fun w : ℂ => w - x) ?_
  exact cur_γ_eq_of_le_threeEighth T i (by nlinarith [t.2.1, Real.pi_pos])
    (by nlinarith [t.2.2, Real.pi_pos])

theorem incOn_cur_agree_high (i : Bool) (x : ℂ) :
    Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x Real.pi (2 * Real.pi)
      = Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x Real.pi (2 * Real.pi) := by
  unfold Work.SphereJordan.incOn
  apply Work.SphereJordan.pathIncTot_congr
  intro t
  refine congrArg (fun w : ℂ => w - x) ?_
  exact cur_γ_eq_of_pi_le T i (by nlinarith [t.2.1, Real.pi_pos])
    (by nlinarith [t.2.2, Real.pi_pos])

/-- The increment of `∂D₁` over two arcs, one reversed, is the increment over a full period. -/
theorem incOn_discCurve_diff (x : ℂ)
    (hcirc : ∀ ψ : ℝ, T.f (Work.Smooth.Jordan.circlePoint ψ) ≠ x) :
    Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq T.θp
      - Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq (T.θp - 2 * Real.pi)
      = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x 0 (2 * Real.pi) := by
  have hav : ∀ s ∈ Set.Icc (T.θp - 2 * Real.pi) T.θp, (discCurve T.f).γ s ≠ x :=
    fun s _ => hcirc s
  have hrev : Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq (T.θp - 2 * Real.pi)
      = - Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x (T.θp - 2 * Real.pi) T.θq :=
    Work.SphereJordan.incOn_rev (discCurve T.f).cont (z := x)
      (a := T.θp - 2 * Real.pi) (b := T.θq) (by linarith [T.hθp_ub])
      (fun s hs => hav s ⟨hs.1, le_trans hs.2 T.hθp_lt.le⟩)
  have hadd := Work.SphereJordan.incOn_add (discCurve T.f).cont (z := x)
    (a := T.θp - 2 * Real.pi) (b := T.θq) (c := T.θp) (by linarith [T.hθp_ub]) T.hθp_lt.le hav
  have hper := Work.SphereJordan.incOn_period (discCurve T.f).cont
    (discCurve T.f).periodic x (fun s => hcirc s) (T.θp - 2 * Real.pi)
  have hw := Work.SphereJordan.incOn_windNumber (discCurve T.f).cont
    (discCurve T.f).periodic x (fun s => hcirc s)
  calc Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq T.θp
        - Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq (T.θp - 2 * Real.pi)
      = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq T.θp
        + Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x (T.θp - 2 * Real.pi) T.θq := by
          rw [hrev]; ring
    _ = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x (T.θp - 2 * Real.pi) T.θp := by
          rw [hadd]; ring
    _ = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x (T.θp - 2 * Real.pi)
          ((T.θp - 2 * Real.pi) + 2 * Real.pi) := by
          rw [show (T.θp - 2 * Real.pi) + 2 * Real.pi = T.θp from by ring]
    _ = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x 0 (2 * Real.pi) := by
          rw [hper, hw]

/-- The same for `∂D₂`. -/
theorem incOn_discCurve_diff_g (x : ℂ)
    (hcirc : ∀ ψ : ℝ, T.g (Work.Smooth.Jordan.circlePoint ψ) ≠ x) :
    Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa (T.φb + 2 * Real.pi)
      - Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa T.φb
      = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x 0 (2 * Real.pi) := by
  have hav : ∀ s ∈ Set.Icc T.φb (T.φb + 2 * Real.pi), (discCurve T.g).γ s ≠ x :=
    fun s _ => hcirc s
  have hrev : Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa T.φb
      = - Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φb T.φa :=
    Work.SphereJordan.incOn_rev (discCurve T.g).cont (z := x)
      (a := T.φb) (b := T.φa) T.hφa_lt.le
      (fun s hs => hav s ⟨hs.1, le_trans hs.2 T.hφa_ub.le⟩)
  have hadd := Work.SphereJordan.incOn_add (discCurve T.g).cont (z := x)
    (a := T.φb) (b := T.φa) (c := T.φb + 2 * Real.pi) T.hφa_lt.le T.hφa_ub.le hav
  have hper := Work.SphereJordan.incOn_period (discCurve T.g).cont
    (discCurve T.g).periodic x (fun s => hcirc s) T.φb
  have hw := Work.SphereJordan.incOn_windNumber (discCurve T.g).cont
    (discCurve T.g).periodic x (fun s => hcirc s)
  calc Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa (T.φb + 2 * Real.pi)
        - Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa T.φb
      = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa (T.φb + 2 * Real.pi)
        + Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φb T.φa := by
          rw [hrev]; ring
    _ = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φb (T.φb + 2 * Real.pi) := by
          rw [hadd]; ring
    _ = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x 0 (2 * Real.pi) := by
          rw [hper, hw]

/-! ## The two flip relations -/

/-- **The flip relation for the `D₁`-boundary arc.** -/
theorem windNumber_cur_arcA_flip (j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur true j).trace) (hx2 : x ∉ (T.cur false j).trace)
    (hcirc : ∀ ψ : ℝ, T.f (Work.Smooth.Jordan.circlePoint ψ) ≠ x) :
    Work.Smooth.SphereJordan.windNumber (T.cur true j).γ (T.cur true j).cont x
      - Work.Smooth.SphereJordan.windNumber (T.cur false j).γ (T.cur false j).cont x
      = Work.Smooth.SphereJordan.windNumber (discCurve T.f).γ (discCurve T.f).cont x := by
  set κ : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hκdef
  have hκ : κ ≠ 0 := by
    rw [hκdef]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hav1 : ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (T.cur true j).γ s ≠ x := fun s _ h => hx1 ⟨s, h⟩
  have hav2 : ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (T.cur false j).γ s ≠ x := fun s _ h => hx2 ⟨s, h⟩
  have e1 := Work.SphereJordan.incOn_add (T.cur true j).cont (z := x) (a := 0) (b := Real.pi / 2)
    (c := 2 * Real.pi) (by positivity) (by nlinarith [Real.pi_pos]) hav1
  have e2 := Work.SphereJordan.incOn_add (T.cur false j).cont (z := x) (a := 0) (b := Real.pi / 2)
    (c := 2 * Real.pi) (by positivity) (by nlinarith [Real.pi_pos]) hav2
  have w1 : Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x 0 (2 * Real.pi)
      = ((Work.Smooth.SphereJordan.windNumber (T.cur true j).γ (T.cur true j).cont x : ℤ) : ℂ) * κ := by
    rw [Work.SphereJordan.incOn_windNumber (T.cur true j).cont
      (T.cur true j).periodic x (fun s h => hx1 ⟨s, h⟩), hκdef]
  have w2 : Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x 0 (2 * Real.pi)
      = ((Work.Smooth.SphereJordan.windNumber (T.cur false j).γ (T.cur false j).cont x : ℤ) : ℂ) * κ := by
    rw [Work.SphereJordan.incOn_windNumber (T.cur false j).cont
      (T.cur false j).periodic x (fun s h => hx2 ⟨s, h⟩), hκdef]
  have wΓ : Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x 0 (2 * Real.pi)
      = ((Work.Smooth.SphereJordan.windNumber (discCurve T.f).γ (discCurve T.f).cont x : ℤ) : ℂ) * κ := by
    rw [Work.SphereJordan.incOn_windNumber (discCurve T.f).cont
      (discCurve T.f).periodic x (fun s => hcirc s), hκdef]
  have hmain : Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x 0 (2 * Real.pi)
      - Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x 0 (2 * Real.pi)
      = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x 0 (2 * Real.pi) := by
    have hagg := incOn_cur_agree T j x
    have hf1 := incOn_cur_first_true T j x
    have hf2 := incOn_cur_first_false T j x
    have hd := incOn_discCurve_diff T x hcirc
    calc Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x 0 (2 * Real.pi)
          - Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x 0 (2 * Real.pi)
        = (Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x 0 (Real.pi / 2)
            + Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x (Real.pi / 2) (2 * Real.pi))
          - (Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x 0 (Real.pi / 2)
            + Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x (Real.pi / 2) (2 * Real.pi)) := by
            rw [e1, e2]
      _ = Work.SphereJordan.incOn (T.cur true j).γ (T.cur true j).cont x 0 (Real.pi / 2)
          - Work.SphereJordan.incOn (T.cur false j).γ (T.cur false j).cont x 0 (Real.pi / 2) := by
            rw [hagg]; ring
      _ = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq T.θp
          - Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x T.θq (T.θp - 2 * Real.pi) := by
            rw [hf1, hf2]
      _ = Work.SphereJordan.incOn (discCurve T.f).γ (discCurve T.f).cont x 0 (2 * Real.pi) := hd
  rw [w1, w2, wΓ] at hmain
  have hcast : (((Work.Smooth.SphereJordan.windNumber (T.cur true j).γ (T.cur true j).cont x
      - Work.Smooth.SphereJordan.windNumber (T.cur false j).γ (T.cur false j).cont x : ℤ)) : ℂ) * κ
      = ((Work.Smooth.SphereJordan.windNumber (discCurve T.f).γ (discCurve T.f).cont x : ℤ) : ℂ) * κ := by
    rw [Int.cast_sub, sub_mul]
    exact hmain
  exact Int.cast_inj.mp (mul_right_cancel₀ hκ hcast)

/-- **The flip relation for the `D₂`-boundary arc.** -/
theorem windNumber_cur_arcB_flip (i : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur i true).trace) (hx2 : x ∉ (T.cur i false).trace)
    (hcirc : ∀ ψ : ℝ, T.g (Work.Smooth.Jordan.circlePoint ψ) ≠ x) :
    Work.Smooth.SphereJordan.windNumber (T.cur i true).γ (T.cur i true).cont x
      - Work.Smooth.SphereJordan.windNumber (T.cur i false).γ (T.cur i false).cont x
      = Work.Smooth.SphereJordan.windNumber (discCurve T.g).γ (discCurve T.g).cont x := by
  set κ : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hκdef
  have hκ : κ ≠ 0 := by
    rw [hκdef]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hav1 : ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (T.cur i true).γ s ≠ x := fun s _ h => hx1 ⟨s, h⟩
  have hav2 : ∀ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (T.cur i false).γ s ≠ x := fun s _ h => hx2 ⟨s, h⟩
  have ha := Work.SphereJordan.incOn_add (T.cur i true).cont (z := x) (a := 0) (b := 3 * Real.pi / 4)
    (c := 2 * Real.pi) (by positivity) (by nlinarith [Real.pi_pos]) hav1
  have hb := Work.SphereJordan.incOn_add (T.cur i false).cont (z := x) (a := 0) (b := 3 * Real.pi / 4)
    (c := 2 * Real.pi) (by positivity) (by nlinarith [Real.pi_pos]) hav2
  have ha2 := Work.SphereJordan.incOn_add (T.cur i true).cont (z := x) (a := 3 * Real.pi / 4)
    (b := Real.pi) (c := 2 * Real.pi) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    (fun s hs => hav1 s ⟨le_trans (by positivity) hs.1, hs.2⟩)
  have hb2 := Work.SphereJordan.incOn_add (T.cur i false).cont (z := x) (a := 3 * Real.pi / 4)
    (b := Real.pi) (c := 2 * Real.pi) (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    (fun s hs => hav2 s ⟨le_trans (by positivity) hs.1, hs.2⟩)
  have w1 : Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x 0 (2 * Real.pi)
      = ((Work.Smooth.SphereJordan.windNumber (T.cur i true).γ (T.cur i true).cont x : ℤ) : ℂ) * κ := by
    rw [Work.SphereJordan.incOn_windNumber (T.cur i true).cont
      (T.cur i true).periodic x (fun s h => hx1 ⟨s, h⟩), hκdef]
  have w2 : Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x 0 (2 * Real.pi)
      = ((Work.Smooth.SphereJordan.windNumber (T.cur i false).γ (T.cur i false).cont x : ℤ) : ℂ) * κ := by
    rw [Work.SphereJordan.incOn_windNumber (T.cur i false).cont
      (T.cur i false).periodic x (fun s h => hx2 ⟨s, h⟩), hκdef]
  have wΓ : Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x 0 (2 * Real.pi)
      = ((Work.Smooth.SphereJordan.windNumber (discCurve T.g).γ (discCurve T.g).cont x : ℤ) : ℂ) * κ := by
    rw [Work.SphereJordan.incOn_windNumber (discCurve T.g).cont
      (discCurve T.g).periodic x (fun s => hcirc s), hκdef]
  have hmain : Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x 0 (2 * Real.pi)
      - Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x 0 (2 * Real.pi)
      = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x 0 (2 * Real.pi) := by
    have hlow := incOn_cur_agree_low T i x
    have hhigh := incOn_cur_agree_high T i x
    have hf1 := incOn_cur_third_true T i x
    have hf2 := incOn_cur_third_false T i x
    have hd := incOn_discCurve_diff_g T x hcirc
    calc Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x 0 (2 * Real.pi)
          - Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x 0 (2 * Real.pi)
        = (Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x 0 (3 * Real.pi / 4)
            + (Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x (3 * Real.pi / 4) Real.pi
              + Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x Real.pi (2 * Real.pi)))
          - (Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x 0 (3 * Real.pi / 4)
            + (Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x (3 * Real.pi / 4) Real.pi
              + Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x Real.pi (2 * Real.pi))) := by
            rw [ha, hb, ha2, hb2]
      _ = Work.SphereJordan.incOn (T.cur i true).γ (T.cur i true).cont x (3 * Real.pi / 4) Real.pi
          - Work.SphereJordan.incOn (T.cur i false).γ (T.cur i false).cont x (3 * Real.pi / 4) Real.pi := by
            rw [hlow, hhigh]; ring
      _ = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa (T.φb + 2 * Real.pi)
          - Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x T.φa T.φb := by
            rw [hf1, hf2]
      _ = Work.SphereJordan.incOn (discCurve T.g).γ (discCurve T.g).cont x 0 (2 * Real.pi) := hd
  rw [w1, w2, wΓ] at hmain
  have hcast : (((Work.Smooth.SphereJordan.windNumber (T.cur i true).γ (T.cur i true).cont x
      - Work.Smooth.SphereJordan.windNumber (T.cur i false).γ (T.cur i false).cont x : ℤ)) : ℂ) * κ
      = ((Work.Smooth.SphereJordan.windNumber (discCurve T.g).γ (discCurve T.g).cont x : ℤ) : ℂ) * κ := by
    rw [Int.cast_sub, sub_mul]
    exact hmain
  exact Int.cast_inj.mp (mul_right_cancel₀ hκ hcast)

end

end Work.Smooth.SphereJordan.ThetaFlip
