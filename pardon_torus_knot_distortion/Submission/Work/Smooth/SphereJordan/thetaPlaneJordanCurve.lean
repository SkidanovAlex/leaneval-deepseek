import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.SphereJordan.planeArcSetup

/-!
# The θ-curve: two disjoint discs joined by two arcs bound a Jordan curve

Two disjoint embedded discs `D₁`, `D₂` in `ℂ` joined by two arcs `α`, `β` whose interiors avoid the
discs and which meet each other only in the discs' interiors (never on the arcs' interiors) form a
"theta graph"; the present file extracts from it a **simple closed plane curve** `K` with

* `range K.γ ⊆ D₁ ∪ D₂ ∪ range α ∪ range β` (the curve uses the two arcs and two small arcs inside
  the discs), and
* `range α ∪ range β ⊆ range K.γ` (it contains both arcs).

The construction is elementary and uses no Jordan–Schoenflies input: inside the disc `D₁` (which is
the image of the model disc `𝔻` under an injective map `f`) the two endpoints `α 0`, `β 0` are
joined by the image of the straight segment between their preimages, and likewise inside `D₂`.
Concretely the proof

1. builds the two "short" arcs as `exists_arc_in_disc` (images of line segments in `𝔻`);
2. concatenates the four arcs as `Path`s (`α`, the arc in `D₂`, `β` reversed, the arc in `D₁`);
3. proves the concatenation injective on all of `[0,1)` from the disjointness of the four pieces;
4. converts the resulting loop `[0,1] → ℂ` into a `2π`-periodic `PlaneCurve` (`loopCurve`), which is
   simple precisely because the loop is injective on `[0,1)`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

local instance instFactTwoPiPosTheta : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-! ## Part 1: from a closed loop on `[0,1]` to a `2π`-periodic plane curve -/

/-- The reparametrisation `x ↦ p (x / 2π)` of a path on `[0,1]`, clamped to `[0,1]`. -/
def loopFn (p : C(Set.Icc (0 : ℝ) 1, ℂ)) : ℝ → ℂ :=
  fun y => Set.IccExtend zero_le_one p (y / (2 * Real.pi))

theorem loopFn_zero (p : C(Set.Icc (0 : ℝ) 1, ℂ)) : loopFn p 0 = p ⟨0, by norm_num⟩ := by
  simp [loopFn, Set.IccExtend_left]

theorem loopFn_two_pi (p : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    loopFn p (2 * Real.pi) = p ⟨1, by norm_num⟩ := by
  simp [loopFn, Set.IccExtend_right]

theorem loopFn_of_mem (p : C(Set.Icc (0 : ℝ) 1, ℂ)) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    loopFn p x = p ⟨x / (2 * Real.pi),
      ⟨div_nonneg hx.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hx.2⟩⟩ :=
  Set.IccExtend_of_mem zero_le_one p
    ⟨div_nonneg hx.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hx.2⟩

/-- **The `2π`-periodic plane curve associated with a closed loop `p` on `[0,1]`.**  The loop is
viewed as a continuous map on the circle `ℝ/2πℤ` via `AddCircle.liftIco`. -/
def loopCurve (p : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hp : p ⟨0, by norm_num⟩ = p ⟨1, by norm_num⟩) : Work.Smooth.Jordan.PlaneCurve where
  γ := fun x => AddCircle.liftIco (2 * Real.pi) 0 (loopFn p) (x : AddCircle (2 * Real.pi))
  cont := by
    have h1 : loopFn p 0 = loopFn p (2 * Real.pi) := by
      rw [loopFn_zero, loopFn_two_pi]; exact hp
    have h2 : ContinuousOn (loopFn p) (Set.Icc 0 (2 * Real.pi)) :=
      (by unfold loopFn; fun_prop : Continuous (loopFn p)).continuousOn
    exact (AddCircle.liftIco_zero_continuous h1 h2).comp (AddCircle.continuous_mk' _)
  periodic := by
    intro x
    show AddCircle.liftIco (2 * Real.pi) 0 (loopFn p)
        ((x + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
      AddCircle.liftIco (2 * Real.pi) 0 (loopFn p) (x : AddCircle (2 * Real.pi))
    rw [AddCircle.coe_add_period]

/-- On one period `[0, 2π)` the curve `loopCurve p` is the loop `p`, reparametrised. -/
theorem loopCurve_apply_of_Ico (p : C(Set.Icc (0 : ℝ) 1, ℂ)) (hp) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    (loopCurve p hp).γ x = loopFn p x := by
  show AddCircle.liftIco (2 * Real.pi) 0 (loopFn p) (x : AddCircle (2 * Real.pi)) = loopFn p x
  exact AddCircle.liftIco_zero_coe_apply hx

/-- **The curve associated with a loop that is injective on `[0,1)` is simple.** -/
theorem loopCurve_isSimple (p : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hp : p ⟨0, by norm_num⟩ = p ⟨1, by norm_num⟩)
    (hinj : Set.InjOn p {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1}) :
    (loopCurve p hp).IsSimple := by
  intro x hx y hy hxy
  rw [Set.mem_Ico] at hx hy
  rw [loopCurve_apply_of_Ico p hp hx, loopCurve_apply_of_Ico p hp hy,
      loopFn_of_mem p ⟨hx.1, hx.2.le⟩, loopFn_of_mem p ⟨hy.1, hy.2.le⟩] at hxy
  have hxlt : x / (2 * Real.pi) < 1 := (div_lt_one Real.two_pi_pos).mpr hx.2
  have hylt : y / (2 * Real.pi) < 1 := (div_lt_one Real.two_pi_pos).mpr hy.2
  have hsub := hinj
    (x₁ := ⟨x / (2 * Real.pi),
      ⟨div_nonneg hx.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hx.2.le⟩⟩)
    hxlt
    (x₂ := ⟨y / (2 * Real.pi),
      ⟨div_nonneg hy.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hy.2.le⟩⟩)
    hylt hxy
  have h2 : x / (2 * Real.pi) = y / (2 * Real.pi) := congrArg Subtype.val hsub
  rw [div_eq_div_iff (ne_of_gt Real.two_pi_pos) (ne_of_gt Real.two_pi_pos)] at h2
  exact mul_right_cancel₀ (ne_of_gt Real.two_pi_pos) h2

/-- The trace of `loopCurve p` is the trace of the loop `p`. -/
theorem range_loopCurve (p : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hp : p ⟨0, by norm_num⟩ = p ⟨1, by norm_num⟩) :
    Set.range (loopCurve p hp).γ = Set.range p := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨b, hb, hbx⟩ := AddCircle.eq_coe_Ico (p := 2 * Real.pi) (x : AddCircle (2 * Real.pi))
    have h1 : (loopCurve p hp).γ x = loopFn p b := by
      show AddCircle.liftIco (2 * Real.pi) 0 (loopFn p) (x : AddCircle (2 * Real.pi)) = loopFn p b
      rw [← hbx]
      exact AddCircle.liftIco_zero_coe_apply hb
    rw [h1, loopFn_of_mem p ⟨hb.1, hb.2.le⟩]
    exact ⟨⟨b / (2 * Real.pi),
      ⟨div_nonneg hb.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hb.2.le⟩⟩, rfl⟩
  · rintro _ ⟨t, rfl⟩
    rcases eq_or_lt_of_le t.2.2 with h | h
    · have ht : t = ⟨1, by norm_num⟩ := Subtype.ext h
      refine ⟨0, ?_⟩
      rw [loopCurve_apply_of_Ico p hp (Set.left_mem_Ico.mpr Real.two_pi_pos), loopFn_zero, ht]
      exact hp
    · refine ⟨2 * Real.pi * (t : ℝ), ?_⟩
      have hlt : (2 * Real.pi) * (t : ℝ) < 2 * Real.pi := by
        nlinarith [Real.two_pi_pos, h]
      have hmem : (2 * Real.pi) * (t : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
        ⟨mul_nonneg Real.two_pi_pos.le t.2.1, hlt⟩
      have hmem2 : (2 * Real.pi) * (t : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
        ⟨hmem.1, hmem.2.le⟩
      have harg : (⟨2 * Real.pi * (t : ℝ) / (2 * Real.pi),
          ⟨div_nonneg hmem2.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hmem2.2⟩⟩
          : Set.Icc (0 : ℝ) 1) = t := by
        apply Subtype.ext
        show 2 * Real.pi * (t : ℝ) / (2 * Real.pi) = (t : ℝ)
        rw [mul_div_cancel_left₀ _ (ne_of_gt Real.two_pi_pos)]
      rw [loopCurve_apply_of_Ico p hp hmem, loopFn_of_mem p hmem2, harg]

/-! ## Part 2: the path library -/

/-- The trace of a concatenation of paths is the union of the traces. -/
theorem path_range_trans {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) : Set.range (p.trans q) = Set.range p ∪ Set.range q := by
  rw [← Path.extend_range (p.trans q), ← Path.extend_range p, ← Path.extend_range q]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨t, rfl⟩
    rcases lt_or_ge (1 / 2) t with h | h
    · rw [Path.extend_trans_of_half_le _ _ h.le]; exact Or.inr ⟨2 * t - 1, rfl⟩
    · rw [Path.extend_trans_of_le_half _ _ h]; exact Or.inl ⟨2 * t, rfl⟩
  · rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · rcases lt_or_ge u 1 with h | h
      · exact ⟨u / 2, by rw [Path.extend_trans_of_le_half _ _ (by linarith),
          show 2 * (u / 2) = u by ring]⟩
      · exact ⟨1 / 2, by rw [Path.extend_of_one_le p h, Path.extend_trans_of_le_half _ _ (by norm_num),
          show 2 * (1 / 2 : ℝ) = 1 by norm_num, Path.extend_of_one_le p le_rfl]⟩
    · rcases lt_or_ge 0 u with h | h
      · exact ⟨(u + 1) / 2, by rw [Path.extend_trans_of_half_le _ _ (by linarith),
          show 2 * ((u + 1) / 2) - 1 = u by ring]⟩
      · exact ⟨1 / 2, by rw [Path.extend_of_le_zero q h, Path.extend_trans_of_le_half _ _ (by norm_num),
          show 2 * (1 / 2 : ℝ) = 1 by norm_num, Path.extend_of_one_le p le_rfl]⟩

/-- The reverse of an injective path is injective. -/
theorem path_injective_symm {X : Type*} [TopologicalSpace X] {x y : X} {p : Path x y}
    (hp : Function.Injective p) : Function.Injective p.symm := by
  intro s t hst
  rw [Path.symm_apply, Path.symm_apply] at hst
  have h2 := congrArg unitInterval.symm (hp hst)
  rwa [unitInterval.symm_symm, unitInterval.symm_symm] at h2

/-- **A concatenation of two injective paths meeting only in the joint endpoint is injective.** -/
theorem path_inj_trans {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y) (q : Path y z)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdisj : Set.range p ∩ Set.range q ⊆ {y}) : Function.Injective (p.trans q) := by
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  rcases lt_or_ge (1 / 2) (s : ℝ) with hs | hs
  · rw [dif_neg (not_le.mpr hs)] at hst
    rcases lt_or_ge (1 / 2) (t : ℝ) with ht | ht
    · rw [dif_neg (not_le.mpr ht)] at hst
      have h2 : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := congrArg Subtype.val (hq hst)
      exact Subtype.ext (by linarith)
    · rw [dif_pos ht] at hst
      have hmem : q ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs], by linarith [s.2.2]⟩⟩ ∈
          Set.range p ∩ Set.range q :=
        ⟨⟨⟨2 * (t : ℝ), ⟨by linarith [t.2.1], by linarith [ht]⟩⟩, hst.symm⟩, ⟨_, rfl⟩⟩
      have hy : q ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs], by linarith [s.2.2]⟩⟩ = y :=
        Set.mem_singleton_iff.mp (hdisj hmem)
      have h1 : (⟨2 * (t : ℝ), ⟨by linarith [t.2.1], by linarith [ht]⟩⟩
          : ↑unitInterval) = 1 :=
        hp (by rw [← hst, hy]; exact (Path.target p).symm)
      have h2 : (⟨2 * (s : ℝ) - 1, ⟨by linarith [hs], by linarith [s.2.2]⟩⟩
          : ↑unitInterval) = 0 :=
        hq (by rw [hy]; exact (Path.source q).symm)
      refine Subtype.ext ?_
      have h1' : 2 * (t : ℝ) = 1 := by simpa using congrArg Subtype.val h1
      have h2' : 2 * (s : ℝ) - 1 = 0 := by simpa using congrArg Subtype.val h2
      linarith
  · rw [dif_pos hs] at hst
    rcases lt_or_ge (1 / 2) (t : ℝ) with ht | ht
    · rw [dif_neg (not_le.mpr ht)] at hst
      have hmem : p ⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs]⟩⟩ ∈
          Set.range p ∩ Set.range q :=
        ⟨⟨_, rfl⟩, ⟨⟨2 * (t : ℝ) - 1, ⟨by linarith [ht], by linarith [t.2.2]⟩⟩, hst.symm⟩⟩
      have hy : p ⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs]⟩⟩ = y :=
        Set.mem_singleton_iff.mp (hdisj hmem)
      have h1 : (⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs]⟩⟩
          : ↑unitInterval) = 1 :=
        hp (by rw [hy]; exact (Path.target p).symm)
      have h2 : (⟨2 * (t : ℝ) - 1, ⟨by linarith [ht], by linarith [t.2.2]⟩⟩
          : ↑unitInterval) = 0 :=
        hq (by rw [← hst, hy]; exact (Path.source q).symm)
      refine Subtype.ext ?_
      have h1' : 2 * (s : ℝ) = 1 := by simpa using congrArg Subtype.val h1
      have h2' : 2 * (t : ℝ) - 1 = 0 := by simpa using congrArg Subtype.val h2
      linarith
    · rw [dif_pos ht] at hst
      have h2 : 2 * (s : ℝ) = 2 * (t : ℝ) := congrArg Subtype.val (hp hst)
      exact Subtype.ext (by linarith)

/-- **A concatenation of two injective paths whose traces meet only in the two ends of the loop is
injective on `[0,1)`.**  This is the injectivity of a "closed loop" built from two halves. -/
theorem path_injOn_trans_loop {X : Type*} [TopologicalSpace X] {a c : X} (P : Path a c)
    (Q : Path c a) (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hdisj : Set.range P ∩ Set.range Q ⊆ {a, c}) :
    Set.InjOn (P.trans Q) {t : ↑unitInterval | (t : ℝ) < 1} := by
  intro s hs t ht hst
  have hslt : (s : ℝ) < 1 := hs
  have htlt : (t : ℝ) < 1 := ht
  rw [Path.trans_apply, Path.trans_apply] at hst
  rcases lt_or_ge (1 / 2) (s : ℝ) with hs' | hs'
  · rw [dif_neg (not_le.mpr hs')] at hst
    rcases lt_or_ge (1 / 2) (t : ℝ) with ht' | ht'
    · rw [dif_neg (not_le.mpr ht')] at hst
      have h2 : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := congrArg Subtype.val (hQ hst)
      exact Subtype.ext (by linarith)
    · rw [dif_pos ht'] at hst
      have hmem : Q ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs'], by linarith [s.2.2]⟩⟩ ∈
          Set.range P ∩ Set.range Q :=
        ⟨⟨⟨2 * (t : ℝ), ⟨by linarith [t.2.1], by linarith [ht']⟩⟩, hst.symm⟩, ⟨_, rfl⟩⟩
      have hval : Q ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs'], by linarith [s.2.2]⟩⟩ = a ∨
          Q ⟨2 * (s : ℝ) - 1, ⟨by linarith [hs'], by linarith [s.2.2]⟩⟩ = c := by
        simpa using hdisj hmem
      rcases hval with hval | hval
      · exfalso
        have hu : (⟨2 * (s : ℝ) - 1, ⟨by linarith [hs'], by linarith [s.2.2]⟩⟩
            : ↑unitInterval) = 1 :=
          hQ (by rw [hval]; exact (Path.target Q).symm)
        have hu' : 2 * (s : ℝ) - 1 = 1 := by simpa using congrArg Subtype.val hu
        linarith
      · have hu : (⟨2 * (s : ℝ) - 1, ⟨by linarith [hs'], by linarith [s.2.2]⟩⟩
            : ↑unitInterval) = 0 :=
          hQ (by rw [hval]; exact (Path.source Q).symm)
        have hw : (⟨2 * (t : ℝ), ⟨by linarith [t.2.1], by linarith [ht']⟩⟩
            : ↑unitInterval) = 1 :=
          hP (by rw [← hst, hval]; exact (Path.target P).symm)
        refine Subtype.ext ?_
        have hu' : 2 * (s : ℝ) - 1 = 0 := by simpa using congrArg Subtype.val hu
        have hw' : 2 * (t : ℝ) = 1 := by simpa using congrArg Subtype.val hw
        linarith
  · rw [dif_pos hs'] at hst
    rcases lt_or_ge (1 / 2) (t : ℝ) with ht' | ht'
    · rw [dif_neg (not_le.mpr ht')] at hst
      have hmem : P ⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs']⟩⟩ ∈
          Set.range P ∩ Set.range Q :=
        ⟨⟨_, rfl⟩, ⟨⟨2 * (t : ℝ) - 1, ⟨by linarith [ht'], by linarith [t.2.2]⟩⟩, hst.symm⟩⟩
      have hval : P ⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs']⟩⟩ = a ∨
          P ⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs']⟩⟩ = c := by
        simpa using hdisj hmem
      rcases hval with hval | hval
      · exfalso
        have hw : (⟨2 * (t : ℝ) - 1, ⟨by linarith [ht'], by linarith [t.2.2]⟩⟩
            : ↑unitInterval) = 1 :=
          hQ (by rw [← hst, hval]; exact (Path.target Q).symm)
        have hw' : 2 * (t : ℝ) - 1 = 1 := by simpa using congrArg Subtype.val hw
        linarith
      · have hw : (⟨2 * (s : ℝ), ⟨by linarith [s.2.1], by linarith [hs']⟩⟩
            : ↑unitInterval) = 1 :=
          hP (by rw [hval]; exact (Path.target P).symm)
        have hu : (⟨2 * (t : ℝ) - 1, ⟨by linarith [ht'], by linarith [t.2.2]⟩⟩
            : ↑unitInterval) = 0 :=
          hQ (by rw [← hst, hval]; exact (Path.source Q).symm)
        refine Subtype.ext ?_
        have hw' : 2 * (s : ℝ) = 1 := by simpa using congrArg Subtype.val hw
        have hu' : 2 * (t : ℝ) - 1 = 0 := by simpa using congrArg Subtype.val hu
        linarith
    · rw [dif_pos ht'] at hst
      have h2 : 2 * (s : ℝ) = 2 * (t : ℝ) := congrArg Subtype.val (hP hst)
      exact Subtype.ext (by linarith)

/-! ## Part 3: an arc inside an embedded disc -/

/-- **Two points of the image of an embedded disc are joined by an injective arc inside it.**
The arc is the image of the straight segment between the two preimages, which lies in `𝔻` by
convexity. -/
theorem exists_arc_in_disc {f : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hf : Function.Injective f)
    {P Q : ℂ} (hP : P ∈ Set.range f) (hQ : Q ∈ Set.range f) (hPQ : P ≠ Q) :
    ∃ arc : C(Set.Icc (0 : ℝ) 1, ℂ), Function.Injective arc ∧
      arc ⟨0, by norm_num⟩ = P ∧ arc ⟨1, by norm_num⟩ = Q ∧ Set.range arc ⊆ Set.range f := by
  obtain ⟨u, rfl⟩ := hP
  obtain ⟨v, rfl⟩ := hQ
  have huv : (u : ℂ) ≠ (v : ℂ) := fun h => hPQ (congrArg f (Subtype.ext h))
  have hconv := convex_closedBall (0 : ℂ) 1
  have hmem : ∀ t : Set.Icc (0 : ℝ) 1,
      (1 - (t : ℝ)) * (u : ℂ) + (t : ℝ) * (v : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro t
    have h := hconv (x := (u : ℂ)) (y := (v : ℂ)) u.2 v.2 (a := 1 - (t : ℝ)) (b := (t : ℝ))
      (by linarith [t.2.2]) t.2.1 (by ring)
    simp only [Algebra.smul_def, Complex.coe_algebraMap] at h
    simpa using h
  let zc : C(Set.Icc (0 : ℝ) 1, Work.Smooth.SphereJordan.Disc) :=
    ⟨fun t => ⟨(1 - (t : ℝ)) * (u : ℂ) + (t : ℝ) * (v : ℂ), hmem t⟩,
      Continuous.subtype_mk (by fun_prop) hmem⟩
  refine ⟨f.comp zc, hf.comp ?_, ?_, ?_, ?_⟩
  · intro s t hst
    have h : (1 - (s : ℝ)) * (u : ℂ) + (s : ℝ) * (v : ℂ) =
        (1 - (t : ℝ)) * (u : ℂ) + (t : ℝ) * (v : ℂ) := congrArg Subtype.val hst
    have h2 : (((t : ℝ) - s : ℝ) : ℂ) * ((u : ℂ) - (v : ℂ)) = 0 := by
      push_cast
      linear_combination h
    rcases mul_eq_zero.mp h2 with hh | hh
    · exact Subtype.ext (by have := Complex.ofReal_eq_zero.mp hh; linarith)
    · exact absurd (sub_eq_zero.mp hh) huv
  · show f (zc ⟨0, by norm_num⟩) = f u
    congr 1
    exact Subtype.ext (by simp [zc])
  · show f (zc ⟨1, by norm_num⟩) = f v
    congr 1
    exact Subtype.ext (by simp [zc])
  · rintro _ ⟨t, rfl⟩
    exact ⟨zc t, rfl⟩

/-! ## Part 4: the theorem -/

theorem thetaPlaneJordanCurve
    {D₁ D₂ : Set ℂ}
    (f : C(Work.Smooth.SphereJordan.Disc, ℂ)) (hf : Function.Injective f)
    (hD₁ : Set.range f = D₁)
    (g : C(Work.Smooth.SphereJordan.Disc, ℂ)) (hg : Function.Injective g)
    (hD₂ : Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α)
    (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ K : Work.Smooth.Jordan.PlaneCurve, K.IsSimple ∧
      Set.range K.γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β ∧
      Set.range α ⊆ Set.range K.γ ∧ Set.range β ⊆ Set.range K.γ := by
  classical
  -- the two short arcs inside the discs
  obtain ⟨A₂, hA₂inj, hA₂₀, hA₂₁, hA₂r⟩ :=
    exists_arc_in_disc hg (by rw [hD₂]; exact hα₁) (by rw [hD₂]; exact hβ₁) hαβ₁
  obtain ⟨A₄, hA₄inj, hA₄₀, hA₄₁, hA₄r⟩ :=
    exists_arc_in_disc hf (by rw [hD₁]; exact hβ₀) (by rw [hD₁]; exact hα₀) hαβ₀.symm
  have hA₂D : Set.range A₂ ⊆ D₂ := by rw [← hD₂]; exact hA₂r
  have hA₄D : Set.range A₄ ⊆ D₁ := by rw [← hD₁]; exact hA₄r
  -- where the four arcs meet the discs
  have hαD₂ : Set.range α ∩ D₂ = {α ⟨1, by norm_num⟩} :=
    range_inter_right hdisj hα₀ hα₁ hαint
  have hαD₁ : Set.range α ∩ D₁ = {α ⟨0, by norm_num⟩} :=
    range_inter_left hdisj hα₀ hα₁ hαint
  have hβD₂ : Set.range β ∩ D₂ = {β ⟨1, by norm_num⟩} :=
    range_inter_right hdisj hβ₀ hβ₁ hβint
  have hβD₁ : Set.range β ∩ D₁ = {β ⟨0, by norm_num⟩} :=
    range_inter_left hdisj hβ₀ hβ₁ hβint
  have hdisjαβ : Disjoint (Set.range α) (Set.range β) :=
    disjoint_range_of_ends hdisj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  have hαβempty : Set.range α ∩ Set.range β = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisjαβ
  have hDempty : D₁ ∩ D₂ = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  -- the four arcs as paths
  let P₁ : Path (α ⟨0, by norm_num⟩) (α ⟨1, by norm_num⟩) := ⟨α, rfl, rfl⟩
  let P₂ : Path (α ⟨1, by norm_num⟩) (β ⟨1, by norm_num⟩) := ⟨A₂, hA₂₀, hA₂₁⟩
  let P₃ : Path (β ⟨0, by norm_num⟩) (β ⟨1, by norm_num⟩) := ⟨β, rfl, rfl⟩
  let P₄ : Path (β ⟨0, by norm_num⟩) (α ⟨0, by norm_num⟩) := ⟨A₄, hA₄₀, hA₄₁⟩
  let P : Path (α ⟨0, by norm_num⟩) (β ⟨1, by norm_num⟩) := P₁.trans P₂
  let Q : Path (β ⟨1, by norm_num⟩) (α ⟨0, by norm_num⟩) := P₃.symm.trans P₄
  let L : Path (α ⟨0, by norm_num⟩) (α ⟨0, by norm_num⟩) := P.trans Q
  have hr₁ : Set.range (P₁ : ↑unitInterval → ℂ) = Set.range α := rfl
  have hr₂ : Set.range (P₂ : ↑unitInterval → ℂ) = Set.range A₂ := rfl
  have hr₃ : Set.range (P₃ : ↑unitInterval → ℂ) = Set.range β := rfl
  have hr₄ : Set.range (P₄ : ↑unitInterval → ℂ) = Set.range A₄ := rfl
  -- pairwise intersections of the four arcs
  have h₁₂ : Set.range P₁ ∩ Set.range P₂ ⊆ {α ⟨1, by norm_num⟩} := by
    rw [hr₁, hr₂]
    intro x ⟨hx₁, hx₂⟩
    have hx : x ∈ Set.range α ∩ D₂ := ⟨hx₁, hA₂D hx₂⟩
    rwa [hαD₂] at hx
  have h₃₄ : Set.range P₃.symm ∩ Set.range P₄ ⊆ {β ⟨0, by norm_num⟩} := by
    rw [Path.symm_range, hr₃, hr₄]
    intro x ⟨hx₁, hx₂⟩
    have hx : x ∈ Set.range β ∩ D₁ := ⟨hx₁, hA₄D hx₂⟩
    rwa [hβD₁] at hx
  have hPQ : Set.range P ∩ Set.range Q ⊆
      {α ⟨0, by norm_num⟩, β ⟨1, by norm_num⟩} := by
    have hP : Set.range P = Set.range α ∪ Set.range A₂ := by
      rw [show P = P₁.trans P₂ from rfl, path_range_trans, hr₁, hr₂]
    have hQ : Set.range Q = Set.range β ∪ Set.range A₄ := by
      rw [show Q = P₃.symm.trans P₄ from rfl, path_range_trans, Path.symm_range, hr₃, hr₄]
    rw [hP, hQ]
    rintro x ⟨hx | hx, hy | hy⟩
    · exfalso
      exact (Set.eq_empty_iff_forall_notMem.mp hαβempty x) ⟨hx, hy⟩
    · have hx' : x ∈ Set.range α ∩ D₁ := ⟨hx, hA₄D hy⟩
      rw [hαD₁] at hx'
      exact Set.mem_insert_iff.mpr (Or.inl hx')
    · have hy' : x ∈ Set.range β ∩ D₂ := ⟨hy, hA₂D hx⟩
      rw [hβD₂] at hy'
      exact Set.mem_insert_iff.mpr (Or.inr hy')
    · exfalso
      exact (Set.eq_empty_iff_forall_notMem.mp hDempty x) ⟨hA₄D hy, hA₂D hx⟩
  -- injectivity of the halves and of the loop
  have hPinj : Function.Injective P := path_inj_trans P₁ P₂ hαinj hA₂inj h₁₂
  have hQinj : Function.Injective Q :=
    path_inj_trans P₃.symm P₄ (path_injective_symm hβinj) hA₄inj h₃₄
  have hLinj : Set.InjOn (⇑L) {t : ↑unitInterval | (t : ℝ) < 1} :=
    path_injOn_trans_loop P Q hPinj hQinj hPQ
  -- the ranges
  have hrangeL : Set.range (⇑(L : C(Set.Icc (0 : ℝ) 1, ℂ))) =
      Set.range α ∪ Set.range β ∪ Set.range A₂ ∪ Set.range A₄ := by
    show Set.range (⇑L) = Set.range α ∪ Set.range β ∪ Set.range A₂ ∪ Set.range A₄
    rw [show L = P.trans Q from rfl, path_range_trans,
      show P = P₁.trans P₂ from rfl, path_range_trans,
      show Q = P₃.symm.trans P₄ from rfl, path_range_trans, Path.symm_range,
      hr₁, hr₂, hr₃, hr₄]
    ext x
    simp only [Set.mem_union]
    tauto
  refine ⟨loopCurve (L : C(Set.Icc (0 : ℝ) 1, ℂ)) ((Path.source L).trans (Path.target L).symm),
    ?_, ?_, ?_, ?_⟩
  · exact loopCurve_isSimple _ _ hLinj
  · rw [range_loopCurve]
    rw [hrangeL]
    intro x hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
    · exact Or.inl (Or.inl (Or.inr (hA₂D hx)))
    · exact Or.inl (Or.inl (Or.inl (hA₄D hx)))
  · rw [range_loopCurve, hrangeL]
    intro x hx
    exact Or.inl (Or.inl (Or.inl hx))
  · rw [range_loopCurve, hrangeL]
    intro x hx
    exact Or.inl (Or.inl (Or.inr hx))

end

end Work.Smooth.SphereJordan
