import Mathlib
import Submission.Work.HornSC.Toolkit
import Submission.Work.HornSC.subinterval_in_rect

namespace Work.HornSC

open Set

/-- **A wall blocks a path.**  Let `V : ℝ → ℂ` be a continuous "wall" whose values on `[-1,1]`
lie in the rectangle `[X,Y] × [-η,η]` and which joins the bottom edge (`V(-1).im = -η`) to the
top edge (`V(1).im = η`).  Let `ρ : ℝ → ℂ` be a path whose values on `[0,1]` lie in the strip
`|im| ≤ η` and which starts strictly to the left of the wall (`ρ(0).re < X`) and ends strictly to
the right of it (`Y < ρ(1).re`).  Then `ρ` and `V` meet.

Proof: cut out of `ρ` the sub-path running from the left side of the rectangle to its right side
(staying inside the rectangle, `subinterval_in_rect`); that path and `V` join opposite pairs of
sides of the rectangle, so Maehara's rectangle crossing lemma (`crossing_lemma_rect`) forces them
to meet. -/
theorem wall_blocks_path {η X Y : ℝ} (hXY : X < Y) {V : C(ℝ, ℂ)}
    (hV : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (V t).re ∈ Set.Icc X Y ∧ (V t).im ∈ Set.Icc (-η) η)
    (hVm : (V (-1)).im = -η) (hVp : (V 1).im = η)
    {ρ : C(ℝ, ℂ)} (hρ : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → |(ρ t).im| ≤ η)
    (hρ0 : (ρ 0).re < X) (hρ1 : Y < (ρ 1).re) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, ∃ s ∈ Set.Icc (-1:ℝ) 1, ρ t = V s := by
  -- Cut out a sub-path of `ρ` running from the left side to the right side of the rectangle,
  -- staying inside it.
  obtain ⟨a, b, ha0, hab, hb1, haX, hbY, hrect⟩ :=
    subinterval_in_rect (Complex.continuous_re.comp ρ.continuous) hXY hρ0 hρ1
  -- Reparametrise that sub-path to the parameter interval `[-1,1]`.
  let φ : ℝ → ℝ := fun t => a + (t + 1) / 2 * (b - a)
  have hφ_cont : Continuous φ := by simp only [φ]; fun_prop
  let h : C(ℝ, ℂ) := ρ.comp ⟨φ, hφ_cont⟩
  have hh_val : ∀ t : ℝ, h t = ρ (φ t) := fun t => by simp [h]
  have hφ_mem : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → φ t ∈ Set.Icc a b := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hu0 : 0 ≤ (t + 1) / 2 := by linarith
    have hu1 : (t + 1) / 2 ≤ 1 := by linarith
    have hba : 0 ≤ b - a := by linarith
    constructor
    · have : 0 ≤ (t + 1) / 2 * (b - a) := mul_nonneg hu0 hba
      simp only [φ]; linarith
    · have hstep : (t + 1) / 2 * (b - a) ≤ b - a := by nlinarith [hu0, hu1, hba]
      simp only [φ]; linarith
  -- The reparametrised sub-path stays in the rectangle.
  have hh : ∀ t ∈ Set.Icc (-1:ℝ) 1, (h t).re ∈ Set.Icc X Y ∧ (h t).im ∈ Set.Icc (-η) η := by
    intro t ht
    have hmem := hφ_mem t ht
    have hmem01 : φ t ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans ha0 hmem.1, le_trans hmem.2 hb1⟩
    constructor
    · rw [hh_val t]; exact hrect (φ t) hmem
    · rw [hh_val t]; exact (abs_le.mp (hρ (φ t) hmem01))
  have h_left : (h (-1)).re = X := by
    have hφ1 : φ (-1) = a := by simp [φ]
    rw [hh_val (-1), hφ1]; exact haX
  have h_right : (h 1).re = Y := by
    have hφ1 : φ 1 = b := by simp only [φ]; ring
    rw [hh_val 1, hφ1]; exact hbY
  -- `h` joins the left and right sides of the rectangle, `V` the bottom and top sides.
  obtain ⟨s, hs, t, ht, hst⟩ :=
    Commons.Topology.Jordan.crossing_lemma_rect (a := X) (b := Y) (c := -η) (d := η)
      h V hh (fun t ht => hV t ht) h_left h_right hVm hVp
  refine ⟨φ s, ⟨le_trans ha0 (hφ_mem s hs).1, le_trans (hφ_mem s hs).2 hb1⟩, t, ht, ?_⟩
  rw [← hh_val s]
  exact hst

end Work.HornSC
