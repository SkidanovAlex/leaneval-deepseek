import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_trans

/-!
# Gluing two loop-level sweeps

If `S₁` and `S₂` are families of regions of the torus with finitely many `2`-surgeries
(`Work.SurgeryInvariance.SweepLoops`) whose endpoint regions match, `S₁.region 1 = S₂.region 0`,
then the two families can be traversed one after the other: there is a single loop-level sweep
whose initial region is `S₁.region 0` and whose final region is `S₂.region 1`.

The glued family is `glueRegion S₁.region S₂.region`: `S₁` is run on `(-∞, 1/2]`, reparametrised by
`t ↦ 2t` and clamped at `0` (so that the family is constant, equal to `S₁.region 0`, for `t ≤ 0`),
and `S₂` is run on `[1/2, ∞)`, reparametrised by `t ↦ 2t - 1` and clamped at `1` (so that it is
constant, equal to `S₂.region 1`, for `t ≥ 1`).  At the junction `t = 1/2` the two pieces agree:
the region there is `S₁.region 1 = S₂.region 0`.

The only point that requires care is the junction: a small neighbourhood of `t = 1/2` contains
parameters on both sides, and the loop content of the two sides has to be compared through the
common region `S₁.region 1 = S₂.region 0`, using the local description of the two sweeps at
`S₁`'s parameter `1` and `S₂`'s parameter `0`.  The exceptional set `glueExc` is the union of the
exceptional parameters of the two sweeps (rescaled, restricted to their effective range `[0,1]`)
together with the junction `1/2`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble.Sweep

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The region function obtained by gluing two sweeps: `S₁` runs on `(-∞, 1/2]` (rescaled by
`t ↦ 2t` and clamped at `0`), `S₂` on `[1/2, ∞)` (rescaled by `t ↦ 2t - 1` and clamped at `1`).
The two pieces agree at the junction `t = 1/2`, where the region is `S₁.region 1 = S₂.region 0`. -/
def glueRegion (R₁ R₂ : ℝ → Set R3) (t : ℝ) : Set R3 :=
  if t ≤ 0 then R₁ 0 else if t ≤ 1 / 2 then R₁ (2 * t) else
    if t ≤ 1 then R₂ (2 * t - 1) else R₂ 1

/-- The exceptional set of the glued sweep: the exceptional parameters of `S₁` (rescaled by
`x ↦ x/2`, restricted to `0 ≤ x ≤ 1`), those of `S₂` (rescaled by `x ↦ (x+1)/2`, restricted to
`0 ≤ x ≤ 1`), and the junction `1/2`. -/
def glueExc (e₁ e₂ : Finset ℝ) : Finset ℝ :=
  (e₁.filter (fun x => 0 ≤ x ∧ x ≤ 1)).image (fun x => x / 2) ∪
  (e₂.filter (fun x => 0 ≤ x ∧ x ≤ 1)).image (fun x => (x + 1) / 2) ∪ {1 / 2}

lemma glueRegion_nonpos {R₁ R₂ : ℝ → Set R3} {t : ℝ} (h : t ≤ 0) :
    glueRegion R₁ R₂ t = R₁ 0 := by
  unfold glueRegion
  rw [if_pos h]

lemma glueRegion_zero_le_half {R₁ R₂ : ℝ → Set R3} {t : ℝ} (h0 : 0 ≤ t) (h : t ≤ 1 / 2) :
    glueRegion R₁ R₂ t = R₁ (2 * t) := by
  unfold glueRegion
  rcases eq_or_lt_of_le h0 with ht | ht
  · subst ht; simp
  · rw [if_neg (not_le.mpr ht), if_pos h]

lemma glueRegion_half_le_one {R₁ R₂ : ℝ → Set R3} (hR : R₁ 1 = R₂ 0) {t : ℝ}
    (h : 1 / 2 ≤ t) (h1 : t ≤ 1) :
    glueRegion R₁ R₂ t = R₂ (2 * t - 1) := by
  unfold glueRegion
  rcases eq_or_lt_of_le h with ht | ht
  · subst ht
    rw [if_neg (by norm_num : ¬ ((1 : ℝ) / 2 ≤ 0)), if_pos (le_refl (1 / 2 : ℝ))]
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num]
    exact hR
  · rw [if_neg (not_le.mpr (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) ht)),
      if_neg (not_le.mpr ht), if_pos h1]

lemma glueRegion_one_le {R₁ R₂ : ℝ → Set R3} {t : ℝ} (h : 1 ≤ t) :
    glueRegion R₁ R₂ t = R₂ 1 := by
  unfold glueRegion
  rcases eq_or_lt_of_le h with ht | ht
  · subst ht
    rw [if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 0)), if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2)),
      if_pos (le_refl (1 : ℝ))]
    norm_num
  · rw [if_neg (not_le.mpr (lt_trans (by norm_num : (0 : ℝ) < 1) ht)),
      if_neg (not_le.mpr (lt_trans (by norm_num : (1 : ℝ) / 2 < 1) ht)),
      if_neg (not_le.mpr ht)]

lemma abs_two_mul (a : ℝ) : |2 * a| = 2 * |a| := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

lemma abs_two_mul_sub (a b : ℝ) : |2 * a - 2 * b| = 2 * |a - b| := by
  rw [show (2 : ℝ) * a - 2 * b = 2 * (a - b) by ring, abs_two_mul]

lemma abs_two_mul_sub_one' (a : ℝ) : |2 * a - 1| = 2 * |a - 1 / 2| := by
  rw [show (2 : ℝ) * a - 1 = 2 * (a - 1 / 2) by ring, abs_two_mul]

/-- The exceptional set is finite, so it has positive distance from each point outside it. -/
lemma exists_notMem_glueExc {e₁ e₂ : Finset ℝ} {t : ℝ} (ht : t ∉ glueExc e₁ e₂) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, |s - t| < r → s ∉ glueExc e₁ e₂ := by
  have hclosed : IsClosed (((glueExc e₁ e₂ : Finset ℝ) : Set ℝ)) :=
    (glueExc e₁ e₂).finite_toSet.isClosed
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp hclosed.isOpen_compl t (by simpa using ht)
  exact ⟨r, hr, fun s hs => hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hs)⟩

/-- For `t ∈ [0, 1/2)` outside the exceptional set, the parameter `2t` of `S₁` is non-exceptional. -/
lemma two_mul_notMem_of_notMem_glueExc₁ {e₁ e₂ : Finset ℝ} {t : ℝ}
    (ht : t ∉ glueExc e₁ e₂) (h0 : 0 ≤ t) (h1 : t < 1 / 2) : 2 * t ∉ e₁ := by
  intro hmem
  apply ht
  have hm : 2 * t / 2 ∈ glueExc e₁ e₂ := by
    simp only [glueExc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_singleton]
    left; left
    exact ⟨2 * t, ⟨hmem, by linarith, by linarith⟩, rfl⟩
  rwa [show (2 : ℝ) * t / 2 = t by ring] at hm

/-- For `t ∈ (1/2, 1]` outside the exceptional set, the parameter `2t - 1` of `S₂` is
non-exceptional. -/
lemma two_mul_sub_one_notMem_of_notMem_glueExc₂ {e₁ e₂ : Finset ℝ} {t : ℝ}
    (ht : t ∉ glueExc e₁ e₂) (h0 : 1 / 2 < t) (h1 : t ≤ 1) : 2 * t - 1 ∉ e₂ := by
  intro hmem
  apply ht
  have hm : ((2 * t - 1) + 1) / 2 ∈ glueExc e₁ e₂ := by
    simp only [glueExc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_singleton]
    left; right
    exact ⟨2 * t - 1, ⟨hmem, by linarith, by linarith⟩, rfl⟩
  rwa [show ((2 : ℝ) * t - 1 + 1) / 2 = t by ring] at hm

/-- `0` is non-exceptional for `S₁` if it is outside the glued exceptional set. -/
lemma zero_notMem_of_notMem_glueExc₁ {e₁ e₂ : Finset ℝ}
    (ht : (0 : ℝ) ∉ glueExc e₁ e₂) : (0 : ℝ) ∉ e₁ := by
  intro hmem
  apply ht
  have hm : (0 : ℝ) / 2 ∈ glueExc e₁ e₂ := by
    simp only [glueExc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_singleton]
    left; left
    exact ⟨0, ⟨hmem, by norm_num, by norm_num⟩, by norm_num⟩
  norm_num at hm
  exact hm

/-- `1` is non-exceptional for `S₂` if it is outside the glued exceptional set. -/
lemma one_notMem_of_notMem_glueExc₂ {e₁ e₂ : Finset ℝ}
    (ht : (1 : ℝ) ∉ glueExc e₁ e₂) : (1 : ℝ) ∉ e₂ := by
  intro hmem
  apply ht
  have hm : (1 + 1) / 2 ∈ glueExc e₁ e₂ := by
    simp only [glueExc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_singleton]
    left; right
    exact ⟨1, ⟨hmem, by norm_num, by norm_num⟩, by norm_num⟩
  norm_num at hm
  exact hm

/-- The local description of a loop-level sweep at an arbitrary parameter: either the region
changes by a piece of zero winding span, or it is transported (`SurgeryStepZero` or
`RegionEquivalent`), uniformly on a neighbourhood of the parameter. -/
lemma sweepLoops_local (S : Work.SurgeryInvariance.SweepLoops P) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Work.SurgeryInvariance.SurgeryStepZero P (S.region t) (S.region s) ∨
        Work.SurgeryInvariance.RegionEquivalent P (S.region t) (S.region s) := by
  by_cases ht : t ∈ S.exc
  · exact S.surgery t ht
  · obtain ⟨ε, hε, -, he⟩ := S.regular t ht
    exact ⟨ε, hε, fun s hs => Or.inr (he s hs)⟩

theorem exists_sweepLoops_trans {P : Work.CoreTopology.ParamTorus}
    (S₁ S₂ : Work.SurgeryInvariance.SweepLoops P) (h : S₁.region 1 = S₂.region 0) :
    ∃ S : Work.SurgeryInvariance.SweepLoops P,
      S.region 0 = S₁.region 0 ∧ S.region 1 = S₂.region 1 := by
  classical
  have hloc₁ := sweepLoops_local S₁
  have hloc₂ := sweepLoops_local S₂
  refine ⟨⟨glueRegion S₁.region S₂.region, glueExc S₁.exc S₂.exc, ?_, ?_⟩,
    glueRegion_nonpos (le_refl (0 : ℝ)), glueRegion_one_le (le_refl (1 : ℝ))⟩
  · -- ## the regular clause
    intro t ht
    obtain ⟨r, hr, hrball⟩ := exists_notMem_glueExc ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · -- `t < 0`: the glued family is constant, equal to `S₁.region 0`
      refine ⟨min r (-t), lt_min hr (by linarith), ?_, ?_⟩
      · intro s hs
        exact hrball s (lt_of_lt_of_le hs (min_le_left r (-t)))
      · intro s hs
        have hst : s < 0 := by
          have h' : s - t < -t := (abs_lt.mp (lt_of_lt_of_le hs (min_le_right r (-t)))).2
          linarith
        rw [glueRegion_nonpos (le_of_lt hlt), glueRegion_nonpos (le_of_lt hst)]
        exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S₁.region 0)
    · -- `t = 0`
      subst heq
      have h0exc : (0 : ℝ) ∉ S₁.exc := zero_notMem_of_notMem_glueExc₁ ht
      obtain ⟨ε₁, hε₁, -, hEq₁⟩ := S₁.regular 0 h0exc
      refine ⟨min r (min (ε₁ / 2) (1 / 4)),
        lt_min hr (lt_min (by linarith) (by norm_num)), ?_, ?_⟩
      · intro s hs
        exact hrball s (lt_of_lt_of_le hs (min_le_left r (min (ε₁ / 2) (1 / 4))))
      · intro s hs
        have hsρ : |s - 0| < min (ε₁ / 2) (1 / 4) :=
          lt_of_lt_of_le hs (min_le_right r (min (ε₁ / 2) (1 / 4)))
        have hsε : |s| < ε₁ / 2 := by
          have h1 := lt_of_lt_of_le hsρ (min_le_left (ε₁ / 2) (1 / 4))
          rwa [sub_zero] at h1
        have hs4 : |s| < 1 / 4 := by
          have h1 := lt_of_lt_of_le hsρ (min_le_right (ε₁ / 2) (1 / 4))
          rwa [sub_zero] at h1
        by_cases hle : s ≤ 0
        · rw [glueRegion_nonpos (le_refl (0 : ℝ)), glueRegion_nonpos hle]
          exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S₁.region 0)
        · have hs0 : 0 < s := not_le.mp hle
          have hs12 : s ≤ 1 / 2 := by linarith [(abs_lt.mp hs4).2]
          rw [glueRegion_nonpos (le_refl (0 : ℝ)), glueRegion_zero_le_half (le_of_lt hs0) hs12]
          refine hEq₁ (2 * s) ?_
          rw [show (2 : ℝ) * s - 0 = 2 * s by ring, abs_two_mul]
          linarith
    · -- `0 < t`
      rcases lt_trichotomy t (1 / 2) with h12 | heq12 | h12'
      · -- `0 < t < 1/2`
        have h2t : 2 * t ∉ S₁.exc :=
          two_mul_notMem_of_notMem_glueExc₁ ht (le_of_lt hgt) h12
        obtain ⟨ε₁, hε₁, -, hEq₁⟩ := S₁.regular (2 * t) h2t
        refine ⟨min r (min (ε₁ / 2) (min t (1 / 2 - t))),
          lt_min hr (lt_min (by linarith) (lt_min hgt (by linarith))), ?_, ?_⟩
        · intro s hs
          exact hrball s (lt_of_lt_of_le hs
            (min_le_left r (min (ε₁ / 2) (min t (1 / 2 - t)))))
        · intro s hs
          have hsρ : |s - t| < min (ε₁ / 2) (min t (1 / 2 - t)) :=
            lt_of_lt_of_le hs (min_le_right r (min (ε₁ / 2) (min t (1 / 2 - t))))
          have hsε : |s - t| < ε₁ / 2 :=
            lt_of_lt_of_le hsρ (min_le_left (ε₁ / 2) (min t (1 / 2 - t)))
          have hst : |s - t| < t :=
            lt_of_lt_of_le hsρ (le_trans (min_le_right (ε₁ / 2) (min t (1 / 2 - t)))
              (min_le_left t (1 / 2 - t)))
          have hs12 : |s - t| < 1 / 2 - t :=
            lt_of_lt_of_le hsρ (le_trans (min_le_right (ε₁ / 2) (min t (1 / 2 - t)))
              (min_le_right t (1 / 2 - t)))
          have hs0 : 0 < s := by linarith [(abs_lt.mp hst).1]
          have hsle : s ≤ 1 / 2 := by linarith [(abs_lt.mp hs12).2]
          rw [glueRegion_zero_le_half (le_of_lt hgt) (le_of_lt h12),
            glueRegion_zero_le_half (le_of_lt hs0) hsle]
          refine hEq₁ (2 * s) ?_
          rw [abs_two_mul_sub]
          linarith
      · -- `t = 1/2` is in the exceptional set
        exact absurd (by rw [heq12]; simp [glueExc]) ht
      · -- `1/2 < t`
        rcases lt_trichotomy t 1 with h1 | heq1 | h1'
        · -- `1/2 < t < 1`
          have h2t : 2 * t - 1 ∉ S₂.exc :=
            two_mul_sub_one_notMem_of_notMem_glueExc₂ ht h12' (le_of_lt h1)
          obtain ⟨ε₂, hε₂, -, hEq₂⟩ := S₂.regular (2 * t - 1) h2t
          refine ⟨min r (min (ε₂ / 2) (min (t - 1 / 2) (1 - t))),
            lt_min hr (lt_min (by linarith) (lt_min (by linarith) (by linarith))), ?_, ?_⟩
          · intro s hs
            exact hrball s (lt_of_lt_of_le hs
              (min_le_left r (min (ε₂ / 2) (min (t - 1 / 2) (1 - t)))))
          · intro s hs
            have hsρ : |s - t| < min (ε₂ / 2) (min (t - 1 / 2) (1 - t)) :=
              lt_of_lt_of_le hs (min_le_right r (min (ε₂ / 2) (min (t - 1 / 2) (1 - t))))
            have hsε : |s - t| < ε₂ / 2 :=
              lt_of_lt_of_le hsρ (min_le_left (ε₂ / 2) (min (t - 1 / 2) (1 - t)))
            have hst : |s - t| < t - 1 / 2 :=
              lt_of_lt_of_le hsρ (le_trans (min_le_right (ε₂ / 2) (min (t - 1 / 2) (1 - t)))
                (min_le_left (t - 1 / 2) (1 - t)))
            have hs1 : |s - t| < 1 - t :=
              lt_of_lt_of_le hsρ (le_trans (min_le_right (ε₂ / 2) (min (t - 1 / 2) (1 - t)))
                (min_le_right (t - 1 / 2) (1 - t)))
            have hs12 : 1 / 2 ≤ s := by linarith [(abs_lt.mp hst).1]
            have hsle : s ≤ 1 := by linarith [(abs_lt.mp hs1).2]
            rw [glueRegion_half_le_one h (le_of_lt h12') (le_of_lt h1),
              glueRegion_half_le_one h hs12 hsle]
            refine hEq₂ (2 * s - 1) ?_
            rw [show (2 : ℝ) * s - 1 - (2 * t - 1) = 2 * (s - t) by ring, abs_two_mul]
            linarith
        · -- `t = 1`
          subst heq1
          have h1exc : (1 : ℝ) ∉ S₂.exc := one_notMem_of_notMem_glueExc₂ ht
          obtain ⟨ε₂, hε₂, -, hEq₂⟩ := S₂.regular 1 h1exc
          refine ⟨min r (min (ε₂ / 2) (1 / 4)),
            lt_min hr (lt_min (by linarith) (by norm_num)), ?_, ?_⟩
          · intro s hs
            exact hrball s (lt_of_lt_of_le hs (min_le_left r (min (ε₂ / 2) (1 / 4))))
          · intro s hs
            have hsρ : |s - 1| < min (ε₂ / 2) (1 / 4) :=
              lt_of_lt_of_le hs (min_le_right r (min (ε₂ / 2) (1 / 4)))
            have hsε : |s - 1| < ε₂ / 2 :=
              lt_of_lt_of_le hsρ (min_le_left (ε₂ / 2) (1 / 4))
            have hs4 : |s - 1| < 1 / 4 :=
              lt_of_lt_of_le hsρ (min_le_right (ε₂ / 2) (1 / 4))
            by_cases hle : s ≤ 1
            · have hs12 : 1 / 2 ≤ s := by linarith [(abs_lt.mp hs4).1]
              rw [glueRegion_one_le (le_refl (1 : ℝ)), glueRegion_half_le_one h hs12 hle]
              refine hEq₂ (2 * s - 1) ?_
              rw [show (2 : ℝ) * s - 1 - 1 = 2 * (s - 1) by ring, abs_two_mul]
              linarith
            · have hs1 : 1 ≤ s := le_of_lt (not_le.mp hle)
              rw [glueRegion_one_le (le_refl (1 : ℝ)), glueRegion_one_le hs1]
              exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S₂.region 1)
        · -- `1 < t`: the glued family is constant, equal to `S₂.region 1`
          refine ⟨min r (t - 1), lt_min hr (by linarith), ?_, ?_⟩
          · intro s hs
            exact hrball s (lt_of_lt_of_le hs (min_le_left r (t - 1)))
          · intro s hs
            have hst : 1 < s := by
              have h' := (abs_lt.mp (lt_of_lt_of_le hs (min_le_right r (t - 1)))).1
              linarith
            rw [glueRegion_one_le (le_of_lt h1'), glueRegion_one_le (le_of_lt hst)]
            exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S₂.region 1)
  · -- ## the surgery clause
    intro t ht
    by_cases ht12 : t = 1 / 2
    · -- the junction `t = 1/2`
      subst ht12
      obtain ⟨ε₁, hε₁, hsc₁⟩ := hloc₁ 1
      obtain ⟨ε₂, hε₂, hsc₂⟩ := hloc₂ 0
      refine ⟨min (ε₁ / 2) (min (ε₂ / 2) (1 / 4)),
        lt_min (by linarith) (lt_min (by linarith) (by norm_num)), ?_⟩
      intro s hs
      have hsε₁ : |s - 1 / 2| < ε₁ / 2 :=
        lt_of_lt_of_le hs (min_le_left (ε₁ / 2) (min (ε₂ / 2) (1 / 4)))
      have hsρ : |s - 1 / 2| < min (ε₂ / 2) (1 / 4) :=
        lt_of_lt_of_le hs (min_le_right (ε₁ / 2) (min (ε₂ / 2) (1 / 4)))
      have hsε₂ : |s - 1 / 2| < ε₂ / 2 :=
        lt_of_lt_of_le hsρ (min_le_left (ε₂ / 2) (1 / 4))
      have hs4 : |s - 1 / 2| < 1 / 4 :=
        lt_of_lt_of_le hsρ (min_le_right (ε₂ / 2) (1 / 4))
      by_cases hle : s ≤ 1 / 2
      · have hs0 : 0 ≤ s := by linarith [(abs_lt.mp hs4).1]
        have h2s : |2 * s - 1| < ε₁ := by
          rw [abs_two_mul_sub_one']
          linarith
        have hregt : glueRegion S₁.region S₂.region (1 / 2) = S₁.region 1 := by
          rw [glueRegion_zero_le_half (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_refl (1 / 2 : ℝ)),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num]
        have hreg : glueRegion S₁.region S₂.region s = S₁.region (2 * s) :=
          glueRegion_zero_le_half hs0 hle
        rw [hregt, hreg]
        exact hsc₁ (2 * s) h2s
      · have hs12 : 1 / 2 ≤ s := le_of_lt (not_le.mp hle)
        have hs1 : s ≤ 1 := by linarith [(abs_lt.mp hs4).2]
        have h2s : |2 * s - 1 - 0| < ε₂ := by
          rw [sub_zero, abs_two_mul_sub_one']
          linarith
        have hregt : glueRegion S₁.region S₂.region (1 / 2) = S₂.region 0 := by
          rw [glueRegion_zero_le_half (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_refl (1 / 2 : ℝ)),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num, h]
        have hreg : glueRegion S₁.region S₂.region s = S₂.region (2 * s - 1) :=
          glueRegion_half_le_one h hs12 hs1
        rw [hregt, hreg]
        exact hsc₂ (2 * s - 1) h2s
    · -- the other exceptional parameters
      have htD := ht
      simp only [glueExc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_singleton] at htD
      rcases htD with (⟨x, ⟨⟨hx, hx0, hx1⟩, hxt⟩⟩ | ⟨x, ⟨⟨hx, hx0, hx1⟩, hxt⟩⟩) | ht12'
      · -- `t = x/2` with `x ∈ S₁.exc`
        have ht1 : t ≤ 1 / 2 := by linarith [hxt, hx1]
        have ht0 : 0 ≤ t := by linarith [hxt, hx0]
        rcases lt_or_eq_of_le ht0 with ht0' | ht0''
        · -- `0 < t`
          have htlt : t < 1 / 2 := lt_of_le_of_ne ht1 ht12
          have h2t : 2 * t = x := by linarith [hxt]
          obtain ⟨ε', hε', hsc'⟩ := S₁.surgery x hx
          refine ⟨min (ε' / 2) (min t (1 / 2 - t)),
            lt_min (by linarith) (lt_min ht0' (by linarith [htlt])), ?_⟩
          intro s hs
          have hsε : |s - t| < ε' / 2 :=
            lt_of_lt_of_le hs (min_le_left (ε' / 2) (min t (1 / 2 - t)))
          have hsρ : |s - t| < min t (1 / 2 - t) :=
            lt_of_lt_of_le hs (min_le_right (ε' / 2) (min t (1 / 2 - t)))
          have hst : |s - t| < t := lt_of_lt_of_le hsρ (min_le_left t (1 / 2 - t))
          have hs12 : |s - t| < 1 / 2 - t :=
            lt_of_lt_of_le hsρ (min_le_right t (1 / 2 - t))
          have hs0 : 0 < s := by linarith [(abs_lt.mp hst).1]
          have hsle : s ≤ 1 / 2 := by linarith [(abs_lt.mp hs12).2]
          have hregt : glueRegion S₁.region S₂.region t = S₁.region x := by
            rw [glueRegion_zero_le_half (le_of_lt ht0') ht1]
            rw [h2t]
          have hreg : glueRegion S₁.region S₂.region s = S₁.region (2 * s) :=
            glueRegion_zero_le_half (le_of_lt hs0) hsle
          rw [hregt, hreg]
          refine hsc' (2 * s) ?_
          rw [show (2 : ℝ) * s - x = 2 * (s - t) by rw [← h2t]; ring, abs_two_mul]
          linarith
        · -- `t = 0` (so `x = 0`)
          subst ht0''
          have hx0' : x = 0 := by linarith [hxt]
          subst hx0'
          obtain ⟨ε', hε', hsc'⟩ := S₁.surgery 0 hx
          refine ⟨min (ε' / 2) (1 / 4), lt_min (by linarith) (by norm_num), ?_⟩
          intro s hs
          have hsε : |s| < ε' / 2 := by
            have h1 := lt_of_lt_of_le hs (min_le_left (ε' / 2) (1 / 4))
            rwa [sub_zero] at h1
          have hs4 : |s| < 1 / 4 := by
            have h1 := lt_of_lt_of_le hs (min_le_right (ε' / 2) (1 / 4))
            rwa [sub_zero] at h1
          by_cases hle : s ≤ 0
          · have hregt : glueRegion S₁.region S₂.region 0 = S₁.region 0 :=
              glueRegion_nonpos (le_refl (0 : ℝ))
            have hreg : glueRegion S₁.region S₂.region s = S₁.region 0 :=
              glueRegion_nonpos hle
            rw [hregt, hreg]
            exact Or.inr (Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S₁.region 0))
          · have hs0 : 0 < s := not_le.mp hle
            have hsle : s ≤ 1 / 2 := by linarith [(abs_lt.mp hs4).2]
            have hregt : glueRegion S₁.region S₂.region 0 = S₁.region 0 :=
              glueRegion_nonpos (le_refl (0 : ℝ))
            have hreg : glueRegion S₁.region S₂.region s = S₁.region (2 * s) :=
              glueRegion_zero_le_half (le_of_lt hs0) hsle
            rw [hregt, hreg]
            refine hsc' (2 * s) ?_
            rw [show (2 : ℝ) * s - 0 = 2 * s by ring, abs_two_mul]
            linarith
      · -- `t = (x+1)/2` with `x ∈ S₂.exc`
        have ht12' : 1 / 2 ≤ t := by linarith [hxt, hx0]
        have ht21 : t ≤ 1 := by linarith [hxt, hx1]
        have htgt : 1 / 2 < t := lt_of_le_of_ne ht12' (Ne.symm ht12)
        rcases lt_or_eq_of_le ht21 with ht21' | ht21''
        · -- `t < 1`
          have h2t : 2 * t - 1 = x := by linarith [hxt]
          obtain ⟨ε', hε', hsc'⟩ := S₂.surgery x hx
          refine ⟨min (ε' / 2) (min (t - 1 / 2) (1 - t)),
            lt_min (by linarith) (lt_min (by linarith) (by linarith)), ?_⟩
          intro s hs
          have hsε : |s - t| < ε' / 2 :=
            lt_of_lt_of_le hs (min_le_left (ε' / 2) (min (t - 1 / 2) (1 - t)))
          have hsρ : |s - t| < min (t - 1 / 2) (1 - t) :=
            lt_of_lt_of_le hs (min_le_right (ε' / 2) (min (t - 1 / 2) (1 - t)))
          have hst : |s - t| < t - 1 / 2 :=
            lt_of_lt_of_le hsρ (min_le_left (t - 1 / 2) (1 - t))
          have hs1 : |s - t| < 1 - t :=
            lt_of_lt_of_le hsρ (min_le_right (t - 1 / 2) (1 - t))
          have hs12 : 1 / 2 ≤ s := by linarith [(abs_lt.mp hst).1]
          have hsle : s ≤ 1 := by linarith [(abs_lt.mp hs1).2]
          have hregt : glueRegion S₁.region S₂.region t = S₂.region x := by
            rw [glueRegion_half_le_one h (le_of_lt htgt) (le_of_lt ht21')]
            rw [h2t]
          have hreg : glueRegion S₁.region S₂.region s = S₂.region (2 * s - 1) :=
            glueRegion_half_le_one h hs12 hsle
          rw [hregt, hreg]
          refine hsc' (2 * s - 1) ?_
          rw [show (2 : ℝ) * s - 1 - x = 2 * (s - t) by rw [← h2t]; ring, abs_two_mul]
          linarith
        · -- `t = 1` (so `x = 1`)
          subst ht21''
          have hx1' : x = 1 := by linarith [hxt]
          subst hx1'
          obtain ⟨ε', hε', hsc'⟩ := S₂.surgery 1 hx
          refine ⟨min (ε' / 2) (1 / 4), lt_min (by linarith) (by norm_num), ?_⟩
          intro s hs
          have hsε : |s - 1| < ε' / 2 := lt_of_lt_of_le hs (min_le_left (ε' / 2) (1 / 4))
          have hs4 : |s - 1| < 1 / 4 := lt_of_lt_of_le hs (min_le_right (ε' / 2) (1 / 4))
          by_cases hle : s ≤ 1
          · have hs12 : 1 / 2 ≤ s := by linarith [(abs_lt.mp hs4).1]
            have hregt : glueRegion S₁.region S₂.region 1 = S₂.region 1 :=
              glueRegion_one_le (le_refl (1 : ℝ))
            have hreg : glueRegion S₁.region S₂.region s = S₂.region (2 * s - 1) :=
              glueRegion_half_le_one h hs12 hle
            rw [hregt, hreg]
            refine hsc' (2 * s - 1) ?_
            rw [show (2 : ℝ) * s - 1 - 1 = 2 * (s - 1) by ring, abs_two_mul]
            linarith
          · have hs1 : 1 ≤ s := le_of_lt (not_le.mp hle)
            have hregt : glueRegion S₁.region S₂.region 1 = S₂.region 1 :=
              glueRegion_one_le (le_refl (1 : ℝ))
            have hreg : glueRegion S₁.region S₂.region s = S₂.region 1 :=
              glueRegion_one_le hs1
            rw [hregt, hreg]
            exact Or.inr (Work.SurgeryInvariance.RegionEquivalent.refl (P := P) (S₂.region 1))
      · exact absurd ht12' ht12

end

end Work.BoxShrink.Bubble.Sweep
