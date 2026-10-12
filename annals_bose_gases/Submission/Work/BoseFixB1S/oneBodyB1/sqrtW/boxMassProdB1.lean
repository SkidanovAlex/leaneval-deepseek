import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1P.Prelim
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `boxMassProdB1`

`Work.SmallBoxSliding.boxMass ℓ d u = |B(u)|` is the volume of the sliding box

    B(u) = dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))

(`ℓ > 0`, `0 < d ≤ 1`).  The box `B(u)` is axis-parallel, with

    B(u) = Box3 (boxLo ℓ d u) (boxHi ℓ d u),

so its volume is the product of its side lengths.  With `A = ℓ/2`, `B = ℓd/2`,
`a = ((ℓd)•u) j` the `j`-th side is `min A (a + B) - max (-A) (a - B)`, and for
`B ≤ A` (i.e. `d ≤ 1`) this equals `min (ℓd) (ℓ(1+d)/2 - |a|) = shortSide ℓ d u j`.
Hence

    boxMass ℓ d u = ∏_j max 0 (shortSide ℓ d u j),

the `max 0` being needed exactly in the regime where the small box misses the
big box in direction `j` (so the overlap is empty and the side length negative).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S.oneBodyB1.sqrtW

/-! ## 1. The volume of an axis-parallel box -/

/-- The volume of the product of intervals `∏_j [p_j, q_j]` inside `Fin 3 → ℝ`. -/
lemma cgBoxF_volume (p q : Fin 3 → ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
        (Set.pi Set.univ (fun j : Fin 3 => Set.Icc (p j) (q j)))
      = ∏ j : Fin 3, ENNReal.ofReal (max 0 (q j - p j)) := by
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Real.volume_Icc]
  have h : ENNReal.ofReal (max 0 (q j - p j)) = ENNReal.ofReal (q j - p j) := by
    rcases le_total 0 (q j - p j) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, ENNReal.ofReal_eq_zero.mpr h, ENNReal.ofReal_zero]
  exact h.symm

/-- **The volume of an axis-parallel box** `Box3 p q` in `ℝ³`. -/
lemma volume_Box3 (p q : Fin 3 → ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (Work.BoseFixB1P.Box3 p q)
      = ∏ j : Fin 3, ENNReal.ofReal (max 0 (q j - p j)) := by
  have hcube : MeasurableSet (Work.BoseFixB1P.Box3 p q) :=
    Work.BoseFixB1P.measurableSet_Box3 p q
  have himg : Work.BoseFixB1P.Box3 p q = ⇑Submission.BoseGases.cgEuc3 ''
      (Set.pi Set.univ (fun j : Fin 3 => Set.Icc (p j) (q j))) := by
    ext x
    constructor
    · intro hx
      refine ⟨Submission.BoseGases.cgEuc3.symm x, ?_, ?_⟩
      · rw [Set.mem_pi]
        intro j _
        simpa [Submission.BoseGases.cgEuc3] using hx j
      · simp [Submission.BoseGases.cgEuc3]
    · rintro ⟨y, hy, rfl⟩ j
      simpa [Submission.BoseGases.cgEuc3] using (Set.mem_pi.mp hy) j trivial
  have himgmeas : MeasurableSet (⇑Submission.BoseGases.cgEuc3 ''
      (Set.pi Set.univ (fun j : Fin 3 => Set.Icc (p j) (q j)))) := by
    rw [← himg]; exact hcube
  rw [himg, ← Submission.BoseGases.cgEuc3_mp.map_eq,
    MeasureTheory.Measure.map_apply Submission.BoseGases.cgEuc3.measurable himgmeas,
    Set.preimage_image_eq _ (MeasurableEquiv.injective Submission.BoseGases.cgEuc3)]
  exact cgBoxF_volume p q

/-- **The volume of an axis-parallel box, as a real number.** -/
lemma volBox_Box3 (p q : Fin 3 → ℝ) :
    Work.BoseFixB1P.volBox (Work.BoseFixB1P.Box3 p q)
      = ∏ j : Fin 3, max 0 (q j - p j) := by
  rw [Work.BoseFixB1P.volBox, MeasureTheory.Measure.real_def, volume_Box3,
    ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun j _ => ENNReal.toReal_ofReal (le_max_left 0 _))

/-! ## 2. The `min`/`max` identity behind `boxHi - boxLo = shortSide` -/

/-- For `B ≤ A`, the overlap of the intervals `[-A, A]` and `[a - B, a + B]` is
`min (2B) (A + B - |a|)`.  This is the coordinate-wise content of
`boxHi - boxLo = shortSide`. -/
lemma real_minmax (A B a : ℝ) (hBA : B ≤ A) :
    min A (a + B) - max (-A) (a - B) = min (2 * B) (A + B - |a|) := by
  by_cases ha : 0 ≤ a
  · have habs : |a| = a := abs_of_nonneg ha
    rw [habs]
    rcases le_total a (A - B) with h | h
    · have h1 : min A (a + B) = a + B := min_eq_right (by linarith)
      have h2 : max (-A) (a - B) = a - B := max_eq_right (by linarith)
      have h3 : min (2 * B) (A + B - a) = 2 * B := min_eq_left (by linarith)
      rw [h1, h2, h3]; ring
    · have h1 : min A (a + B) = A := min_eq_left (by linarith)
      have h2 : max (-A) (a - B) = a - B := max_eq_right (by linarith)
      have h3 : min (2 * B) (A + B - a) = A + B - a := min_eq_right (by linarith)
      rw [h1, h2, h3]; ring
  · have ha' : a < 0 := not_le.mp ha
    have habs : A + B - |a| = A + B + a := by rw [abs_of_neg ha']; ring
    rw [habs]
    rcases le_total (B - A) a with h | h
    · have h1 : min A (a + B) = a + B := min_eq_right (by linarith)
      have h2 : max (-A) (a - B) = a - B := max_eq_right (by linarith)
      have h3 : min (2 * B) (A + B + a) = 2 * B := min_eq_left (by linarith)
      rw [h1, h2, h3]; ring
    · have h1 : min A (a + B) = a + B := min_eq_right (by linarith)
      have h2 : max (-A) (a - B) = -A := max_eq_left (by linarith)
      have h3 : min (2 * B) (A + B + a) = A + B + a := min_eq_right (by linarith)
      rw [h1, h2, h3]; ring

/-! ## 3. `shortSide` is the side of `Box3 (boxLo) (boxHi)` -/

lemma boxHi_sub_boxLo_eq_shortSide {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd1 : d ≤ 1)
    (u : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    Work.BoseFixB1P.boxHi ℓ d u j - Work.BoseFixB1P.boxLo ℓ d u j
      = Work.SmallBoxSliding.shortSide ℓ d u j := by
  have hBA : ℓ * d / 2 ≤ ℓ / 2 := by
    have h := mul_le_mul_of_nonneg_left hd1 hℓ.le
    linarith
  have key : ∀ a : ℝ,
      min (ℓ / 2) (a + ℓ * d / 2) - max (-(ℓ / 2)) (a - ℓ * d / 2)
        = min (ℓ * d) (1 / 2 * ℓ * (1 + d) - |a|) := by
    intro a
    have h := real_minmax (ℓ / 2) (ℓ * d / 2) a hBA
    rw [h, show 2 * (ℓ * d / 2) = ℓ * d by ring,
      show ℓ / 2 + ℓ * d / 2 = 1 / 2 * ℓ * (1 + d) by ring]
  simp only [Work.BoseFixB1P.boxHi, Work.BoseFixB1P.boxLo,
    Work.SmallBoxSliding.shortSide]
  exact key (((ℓ * d) • u) j)

/-! ## 4. The main identity -/

theorem boxMassProdB1 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1) (u : EuclideanSpace ℝ (Fin 3)) : Work.SmallBoxSliding.boxMass ℓ d u = ∏ j : Fin 3, max 0 (Work.SmallBoxSliding.shortSide ℓ d u j) := by
  rw [Work.BoseFixB1P.boxMass_eq_volBox ℓ d u, Work.BoseFixB1P.dlBox_eq_Box3 ℓ d u,
    volBox_Box3]
  exact Finset.prod_congr rfl (fun j _ => by
    rw [boxHi_sub_boxLo_eq_shortSide hℓ hd1 u j])

end Work.BoseFixB1S.oneBodyB1.sqrtW
