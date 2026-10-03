import Mathlib

/-!
# Boundedness of a function on a horizontal strip, from `1`-periodicity and two one-sided bounds

If `F : ℂ → ℂ` is `1`-periodic in the real direction on the strip `{w | η < |w.im|}`
and continuous there, and is bounded above for `im → +∞` and below for `im → -∞`,
then `F` is bounded on every (sub)strip `{w | y ≤ |w.im|}` with `y > η`.

The heart of the argument: the real direction collapses onto a fundamental cell
`{0 ≤ re ≤ 1}`, on which the closed slice in the imaginary direction is compact;
the two one-sided hypotheses take care of the unbounded imaginary directions.
-/

namespace Work.Repel

/-- On the strip `η < |Im|` a `1`-periodic function is periodic with respect to every
integer shift: `F (w + n) = F w` for all `n : ℤ`. -/
private lemma periodic_add_int {F : ℂ → ℂ} {η : ℝ}
    (hper : ∀ w : ℂ, η < |w.im| → F (w + 1) = F w) :
    ∀ (w : ℂ) (n : ℤ), η < |w.im| → F (w + (n : ℂ)) = F w := by
  intro w n
  refine Int.induction_on (motive := fun n => η < |w.im| → F (w + (n : ℂ)) = F w) n ?_ ?_ ?_
  · intro _; simp
  · intro i ih h
    have hk : η < |(w + (((i : ℤ)) : ℂ)).im| := by simpa using h
    have hstep : F (w + (((i : ℤ)) : ℂ) + 1) = F (w + (((i : ℤ)) : ℂ)) := hper _ hk
    have heq : w + ((((i : ℤ) + 1 : ℤ)) : ℂ) = w + (((i : ℤ)) : ℂ) + 1 := by push_cast; ring
    rw [heq, hstep]; exact ih h
  · intro i ih h
    set u : ℂ := w + (((-(i : ℤ)) : ℤ) : ℂ) with hu
    have him : (u - 1).im = w.im := by rw [hu]; simp
    have hk : η < |(u - 1).im| := by rw [him]; exact h
    have hstep : F u = F (u - 1) := by
      have h1 := hper (u - 1) hk
      rwa [sub_add_cancel] at h1
    have heq : w + (((-(i : ℤ) - 1 : ℤ)) : ℂ) = u - 1 := by rw [hu]; push_cast; ring
    rw [heq, ← hstep]
    simpa [hu] using ih h

theorem periodic_strip_bound {F : ℂ → ℂ} {η y Cup Cdn : ℝ} (hy : η < y)
    (hCup : 0 ≤ Cup) (hCdn : 0 ≤ Cdn)
    (hper : ∀ w : ℂ, η < |w.im| → F (w + 1) = F w)
    (hcont : ContinuousOn F {w : ℂ | η < |w.im|})
    (hup : ∃ T : ℝ, ∀ w : ℂ, T ≤ w.im → ‖F w‖ ≤ Cup)
    (hdn : ∃ T : ℝ, ∀ w : ℂ, w.im ≤ T → ‖F w‖ ≤ Cdn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, y ≤ |w.im| → ‖F w‖ ≤ C := by
  obtain ⟨Tup, hTup⟩ := hup
  obtain ⟨Tdn, hTdn⟩ := hdn
  have hpero := periodic_add_int hper
  -- membership in the continuity strip
  have strip_of_ge : ∀ {z : ℂ}, y ≤ z.im → η < |z.im| := by
    intro z hz
    exact lt_of_lt_of_le hy (le_trans hz (le_abs_self z.im))
  have strip_of_le : ∀ {z : ℂ}, z.im ≤ -y → η < |z.im| := by
    intro z hz
    have h1 : y ≤ -z.im := by linarith
    have h2 : -z.im ≤ |z.im| := neg_le_abs z.im
    exact lt_of_lt_of_le hy (le_trans h1 h2)
  -- compactness on the two closed slices of the fundamental cell
  have hK1 : IsCompact (Complex.reProdIm (Set.Icc (0:ℝ) 1) (Set.Icc y (max y Tup))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hS1 : Complex.reProdIm (Set.Icc (0:ℝ) 1) (Set.Icc y (max y Tup)) ⊆ {w : ℂ | η < |w.im|} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact strip_of_ge hz.2.1
  obtain ⟨M1, hM1⟩ := hK1.exists_bound_of_continuousOn (hcont.mono hS1)
  have hK2 : IsCompact (Complex.reProdIm (Set.Icc (0:ℝ) 1) (Set.Icc (min (-y) Tdn) (-y))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hS2 : Complex.reProdIm (Set.Icc (0:ℝ) 1) (Set.Icc (min (-y) Tdn) (-y)) ⊆ {w : ℂ | η < |w.im|} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact strip_of_le hz.2.2
  obtain ⟨M2, hM2⟩ := hK2.exists_bound_of_continuousOn (hcont.mono hS2)
  refine ⟨max (max M1 M2) (max Cup Cdn), ?_, ?_⟩
  · have _hC := hCup
    have h1 : (0:ℝ) ≤ max Cup Cdn := le_trans hCdn (le_max_right Cup Cdn)
    exact le_trans h1 (le_max_right (max M1 M2) (max Cup Cdn))
  · intro w hw
    have hstrip : η < |w.im| := lt_of_lt_of_le hy hw
    rcases (le_abs.mp hw) with hpos | hneg
    · -- `w.im ≥ y`: use the upper slice, or the upper bound at infinity
      by_cases hle : w.im ≤ max y Tup
      · set u : ℂ := w - (((⌊w.re⌋ : ℤ)) : ℂ) with hu
        have hure : u.re = w.re - (⌊w.re⌋ : ℝ) := by rw [hu]; simp
        have huim : u.im = w.im := by rw [hu]; simp
        have hmem : u ∈ Complex.reProdIm (Set.Icc (0:ℝ) 1) (Set.Icc y (max y Tup)) := by
          rw [Complex.mem_reProdIm]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
          · rw [hure]; have h := Int.floor_le w.re; linarith
          · rw [hure]; have h := Int.lt_floor_add_one w.re; linarith
          · rw [huim]; exact hpos
          · rw [huim]; exact hle
        have hbound : ‖F u‖ ≤ M1 := hM1 u hmem
        have hFu : F u = F w := by
          have e : u = w + ((-(⌊w.re⌋) : ℤ) : ℂ) := by rw [hu]; push_cast; ring
          rw [e]; exact hpero w (-(⌊w.re⌋)) hstrip
        have : ‖F w‖ = ‖F u‖ := by rw [← hFu]
        rw [this]
        exact le_trans hbound
          (le_trans (le_max_left M1 M2) (le_max_left (max M1 M2) (max Cup Cdn)))
      · have hT : Tup ≤ w.im := le_trans (le_max_right y Tup) (le_of_lt (lt_of_not_ge hle))
        exact le_trans (hTup w hT)
          (le_trans (le_max_left Cup Cdn) (le_max_right (max M1 M2) (max Cup Cdn)))
    · -- `w.im ≤ -y`: use the lower slice, or the lower bound at infinity
      have hneg' : w.im ≤ -y := by linarith
      by_cases hle : min (-y) Tdn ≤ w.im
      · set u : ℂ := w - (((⌊w.re⌋ : ℤ)) : ℂ) with hu
        have hure : u.re = w.re - (⌊w.re⌋ : ℝ) := by rw [hu]; simp
        have huim : u.im = w.im := by rw [hu]; simp
        have hmem : u ∈ Complex.reProdIm (Set.Icc (0:ℝ) 1) (Set.Icc (min (-y) Tdn) (-y)) := by
          rw [Complex.mem_reProdIm]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
          · rw [hure]; have h := Int.floor_le w.re; linarith
          · rw [hure]; have h := Int.lt_floor_add_one w.re; linarith
          · rw [huim]; exact hle
          · rw [huim]; exact hneg'
        have hbound : ‖F u‖ ≤ M2 := hM2 u hmem
        have hFu : F u = F w := by
          have e : u = w + ((-(⌊w.re⌋) : ℤ) : ℂ) := by rw [hu]; push_cast; ring
          rw [e]; exact hpero w (-(⌊w.re⌋)) hstrip
        have : ‖F w‖ = ‖F u‖ := by rw [← hFu]
        rw [this]
        exact le_trans hbound
          (le_trans (le_max_right M1 M2) (le_max_left (max M1 M2) (max Cup Cdn)))
      · have hT : w.im ≤ Tdn := le_trans (le_of_lt (lt_of_not_ge hle)) (min_le_right (-y) Tdn)
        exact le_trans (hTdn w hT)
          (le_trans (le_max_right Cup Cdn) (le_max_right (max M1 M2) (max Cup Cdn)))

end Work.Repel
