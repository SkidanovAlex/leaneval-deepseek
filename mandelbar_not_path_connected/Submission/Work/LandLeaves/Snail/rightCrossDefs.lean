import Mathlib
import Submission.Work.LandLeaves.Snail.barrierDefs
import Submission.Work.LandLeaves.Snail.exists_barrier_min
import Submission.Work.LandLeaves.Snail.leftCross_bddBelow_on_Icc
import Submission.Work.LandLeaves.Snail.leftCross_tendsto_atBot
import Submission.Work.LandLeaves.Snail.pathTail_isClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rightmost barrier point at a given height

`rightCross P t₀ h` is the supremum of the real parts of the barrier points of height `h`,
where the barrier is `pathTail P t₀ = P '' [t₀,∞)` (the image of the tail of a snail path).

The main result here is that `h ↦ rightCross P t₀ h` is **upper semicontinuous**, which is what
makes the set of points that lie strictly to the right of the barrier at their own height both
open and (together with a "no equality in `G`" observation) closed in the region `G`.
-/

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

/-- The set of real parts of the barrier points of height `h`. -/
def barrierFibre (P : ℝ → ℂ) (t₀ h : ℝ) : Set ℝ :=
  (fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h})

lemma leftCross_eq_sInf (P : ℝ → ℂ) (t₀ h : ℝ) :
    leftCross P t₀ h = sInf (barrierFibre P t₀ h) := rfl

/-- **The rightmost barrier point at height `h`**: the supremum of the real parts of the barrier
points of height `h`. -/
noncomputable def rightCross (P : ℝ → ℂ) (t₀ h : ℝ) : ℝ := sSup (barrierFibre P t₀ h)

lemma mem_barrierFibre {P : ℝ → ℂ} {t₀ h : ℝ} {W : ℂ}
    (hW : W ∈ pathTail P t₀) (him : W.im = h) : W.re ∈ barrierFibre P t₀ h :=
  ⟨W, ⟨hW, him⟩, rfl⟩

lemma barrierFibre_nonempty_iff {P : ℝ → ℂ} {t₀ h : ℝ} :
    (barrierFibre P t₀ h).Nonempty ↔ ∃ W ∈ pathTail P t₀, W.im = h := by
  constructor
  · rintro ⟨y, W, ⟨hW, him⟩, rfl⟩
    exact ⟨W, hW, him⟩
  · rintro ⟨W, hW, him⟩
    exact ⟨W.re, mem_barrierFibre hW him⟩

/-- Every point of the barrier has real part `< X₁`. -/
lemma pathTail_re_lt {P : ℝ → ℂ} {t₀ X₁ : ℝ}
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁) :
    ∀ W ∈ pathTail P t₀, W.re < X₁ := by
  intro W hW
  rw [pathTail] at hW
  obtain ⟨u, hu, rfl⟩ := hW
  exact hPt u hu

section Bounds

variable {P : ℝ → ℂ} {t₀ X₁ : ℝ}

lemma rightCross_bddAbove {h : ℝ} (hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁) :
    BddAbove (barrierFibre P t₀ h) :=
  ⟨X₁, by rintro y ⟨W, hW, rfl⟩; exact hB W hW.1⟩

lemma rightCross_le {h : ℝ} (hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁)
    (hne : (barrierFibre P t₀ h).Nonempty) : rightCross P t₀ h ≤ X₁ :=
  csSup_le hne fun _ hy => by rcases hy with ⟨W, hW, rfl⟩; exact hB W hW.1

lemma le_rightCross {h : ℝ} (hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁)
    {W : ℂ} (hW : W ∈ pathTail P t₀) (him : W.im = h) : W.re ≤ rightCross P t₀ h :=
  le_csSup (rightCross_bddAbove hB) (mem_barrierFibre hW him)

lemma leftCross_le_rightCross {h : ℝ} (hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁)
    (hne : (barrierFibre P t₀ h).Nonempty) (hbdd : BddBelow (barrierFibre P t₀ h)) :
    leftCross P t₀ h ≤ rightCross P t₀ h := by
  rw [leftCross_eq_sInf]
  exact csInf_le_csSup hne hbdd (rightCross_bddAbove hB)

lemma lt_rightCross_iff {h a : ℝ} (hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁)
    (hne : (barrierFibre P t₀ h).Nonempty) :
    a < rightCross P t₀ h ↔ ∃ W ∈ pathTail P t₀, W.im = h ∧ a < W.re := by
  rw [rightCross, lt_csSup_iff (rightCross_bddAbove hB) hne]
  constructor
  · rintro ⟨y, ⟨W, hW, rfl⟩, hlt⟩
    exact ⟨W, hW.1, hW.2, hlt⟩
  · rintro ⟨W, hW, him, hlt⟩
    exact ⟨W.re, mem_barrierFibre hW him, hlt⟩

end Bounds

/-- **The barrier meets every horizontal line above its foot.** -/
lemma barrierFibre_nonempty {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T t₀ X₁ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁) {h : ℝ} (hh : (P t₀).im ≤ h) :
    (barrierFibre P t₀ h).Nonempty := by
  have hc2 : 0 < c.im / 2 := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h < (P t₀).im + n * (c.im / 2) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((h - (P t₀).im) / (c.im / 2))
    exact ⟨n, by rw [div_lt_iff₀ hc2] at hn; linarith⟩
  have hgrowth := path_height_growth (F := F) (P := P) (c := c) hheight hPinv htT hPt le_rfl n
  have hgt : h < (P (t₀ + n)).im := lt_of_lt_of_le hn hgrowth
  have hcont : ContinuousOn (fun t : ℝ => (P t).im) (Set.Icc t₀ (t₀ + n)) :=
    Complex.continuous_im.comp_continuousOn (hPc.mono fun t ht => le_trans htT ht.1)
  have hmem : h ∈ Set.Icc ((fun t : ℝ => (P t).im) t₀) ((fun t : ℝ => (P t).im) (t₀ + n)) :=
    ⟨hh, le_of_lt hgt⟩
  obtain ⟨u, hu, hueq⟩ :=
    (intermediate_value_Icc (le_add_of_nonneg_right (Nat.cast_nonneg n)) hcont hmem)
  exact (barrierFibre_nonempty_iff).mpr ⟨P u, ⟨u, hu.1, rfl⟩, hueq⟩

section Compact

variable {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T t₀ X₁ : ℝ}

/-- The part of the barrier of height `h` is compact: the barrier is "proper" in the height. -/
lemma pathTail_fibre_isCompact (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T))
    (htT : T ≤ t₀) (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁) (h : ℝ) :
    IsCompact (pathTail P t₀ ∩ {W : ℂ | W.im = h}) := by
  have him : Tendsto (fun t : ℝ => (P t).im) atTop atTop :=
    tendsto_im_atTop_of_path hc_im hPc htT hheight hPinv hPt
  have hEv : ∀ᶠ t : ℝ in atTop, h + 1 ≤ (P t).im := him.eventually (mem_atTop _)
  rw [eventually_atTop] at hEv
  obtain ⟨t₁, ht₁⟩ := hEv
  have hclosed : IsClosed (pathTail P t₀ ∩ {W : ℂ | W.im = h}) :=
    (pathTail_isClosed hc_im hPc htT hheight hPinv hPt).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  have hcomp : IsCompact (P '' Set.Icc t₀ (max t₁ t₀)) :=
    isCompact_Icc.image_of_continuousOn (hPc.mono fun t ht => le_trans htT ht.1)
  refine hcomp.of_isClosed_subset hclosed ?_
  rintro W ⟨⟨u, hu, rfl⟩, hWim⟩
  have huT : u ≤ max t₁ t₀ := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : t₁ ≤ u := le_trans (le_max_left t₁ t₀) (le_of_lt hcon)
    have := ht₁ u h1
    rw [hWim] at this
    linarith
  exact ⟨u, ⟨hu, huT⟩, rfl⟩

end Compact

/-- The fibre of the barrier over a height is bounded below. -/
lemma barrierFibre_bddBelow_of_isCompact {P : ℝ → ℂ} {t₀ h : ℝ}
    (hK : IsCompact (pathTail P t₀ ∩ {W : ℂ | W.im = h})) :
    BddBelow (barrierFibre P t₀ h) := by
  rcases Set.eq_empty_or_nonempty (pathTail P t₀ ∩ {W : ℂ | W.im = h}) with hemp | hne
  · refine ⟨0, ?_⟩
    rintro y ⟨W, hW, rfl⟩
    rw [hemp] at hW
    exact absurd hW (by simp)
  · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne (f := Complex.re) Complex.continuous_re.continuousOn
    refine ⟨w.re, ?_⟩
    rintro y ⟨W, ⟨hW, him⟩, rfl⟩
    exact hmin ⟨hW, him⟩

/-- **The barrier fibre over any height is bounded below.** -/
lemma barrierFibre_bddBelow {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T t₀ X₁ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁) (h : ℝ) :
    BddBelow (barrierFibre P t₀ h) :=
  barrierFibre_bddBelow_of_isCompact
    (pathTail_fibre_isCompact hc_im hPc htT hheight hPinv hPt h)

/-- **Upper semicontinuity of `rightCross`** in sequence form: a limit of barrier points of
heights `h n → h` has real part at most `rightCross P t₀ h`. -/
lemma rightCross_le_of_tendsto {P : ℝ → ℂ} {t₀ X₁ : ℝ}
    (hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁) (hclosed : IsClosed (pathTail P t₀))
    {w : ℕ → ℂ} (hw : ∀ n, w n ∈ pathTail P t₀) {a : ℕ → ℝ} {h : ℝ}
    (ha : Tendsto a atTop (nhds h))
    (hwim : ∀ n, (w n).im = a n) {L : ℝ} (hL : Tendsto (fun n => (w n).re) atTop (nhds L))
    (hne : (barrierFibre P t₀ h).Nonempty) :
    L ≤ rightCross P t₀ h := by
  have him : Tendsto (fun n => (w n).im) atTop (nhds h) := by
    simpa [hwim] using ha
  have hw' : Tendsto w atTop (nhds (⟨L, h⟩ : ℂ)) := by
    have h1 : Tendsto (fun n => ((w n).re, (w n).im)) atTop (nhds (L, h)) :=
      hL.prodMk_nhds him
    have h2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by continuity
    have h3 : Tendsto (fun n => ((w n).re : ℂ) + ((w n).im : ℂ) * Complex.I) atTop
        (nhds ((L : ℂ) + (h : ℂ) * Complex.I)) := (h2.tendsto (L, h)).comp h1
    have heq : (fun n => ((w n).re : ℂ) + ((w n).im : ℂ) * Complex.I) = w := by
      funext n; exact Complex.re_add_im (w n)
    rw [heq] at h3
    have hpt : ((L : ℂ) + (h : ℂ) * Complex.I) = (⟨L, h⟩ : ℂ) := by
      apply Complex.ext <;> simp
    rwa [hpt] at h3
  have hmem : (⟨L, h⟩ : ℂ) ∈ pathTail P t₀ :=
    hclosed.mem_of_tendsto hw' (Eventually.of_forall hw)
  have : L ≤ rightCross P t₀ h :=
    le_rightCross hB hmem (by simp)
  exact this

end Work.LandLeaves.Snail
