import Mathlib
import Submission.Work.Pert.tSat_glue

namespace Work.Pert.pert2v2

open Set

/-- An integer whose real value has absolute value `< 2` is `-1`, `0` or `1`.  (The window of a
chart of half-width `≤ 1` forces `|n| < 2` for every deck translation `n` that keeps a point inside
the same chart.) -/
lemma glue_window_wide_int_cases {n : ℤ} (h : |((n : ℝ))| < 2) : n = -1 ∨ n = 0 ∨ n = 1 := by
  have h1 : ((n : ℤ) : ℝ) < 2 := (abs_lt.mp h).2
  have h2 : (-2 : ℝ) < ((n : ℤ) : ℝ) := (abs_lt.mp h).1
  have h1' : n < 2 := by exact_mod_cast h1
  have h2' : -2 < n := by exact_mod_cast h2
  omega

/-- **Same-chart shift compatibility from the `+1`-relation.**  If a chart `U` with `R (w+1) = R w + 1`
wherever both points lie in `U` is contained in the window `{|Re - x₀| < R1}` with `R1 ≤ 1`, then the
`+1`-relation propagates to *every* shift that keeps the point inside the chart: for `w, w + n ∈ U`,
`R (w + n) = R w + n`.

The window is what makes this possible: `|Re w - x₀| < R1` and `|Re (w+n) - x₀| < R1` give
`|n| ≤ |Re (w+n) - x₀| + |Re w - x₀| < 2 R1 ≤ 2`, so `n ∈ {-1, 0, 1}`; the case `n = 1` is the
hypothesis, and `n = -1` is the hypothesis applied at `w - 1`. -/
lemma glue_window_wide_shift_compat {x₀ R1 : ℝ} (hR1hi : R1 ≤ 1) {U : Set ℂ} {R : ℂ → ℂ}
    (hR1 : ∀ w : ℂ, w ∈ U → w + 1 ∈ U → R (w + 1) = R w + 1)
    (hwin : U ⊆ {w : ℂ | |w.re - x₀| < R1}) :
    ∀ (n : ℤ) (w : ℂ), w ∈ U → w + (n : ℂ) ∈ U → R (w + (n : ℂ)) = R w + (n : ℂ) := by
  intro n w hw hwn
  have h1 : |w.re - x₀| < R1 := hwin hw
  have h2 : |(w + (n : ℂ)).re - x₀| < R1 := hwin hwn
  have hre : ((n : ℤ) : ℝ) = (w + (n : ℂ)).re - w.re := by simp
  have habs : |((n : ℤ) : ℝ)| < 2 := by
    rw [hre]
    have hsplit : (w + (n : ℂ)).re - w.re = ((w + (n : ℂ)).re - x₀) + (x₀ - w.re) := by ring
    rw [hsplit]
    calc |((w + (n : ℂ)).re - x₀) + (x₀ - w.re)|
        ≤ |(w + (n : ℂ)).re - x₀| + |x₀ - w.re| := abs_add_le _ _
      _ = |(w + (n : ℂ)).re - x₀| + |w.re - x₀| := by rw [abs_sub_comm x₀ w.re]
      _ < R1 + R1 := add_lt_add h2 h1
      _ ≤ 2 := by linarith
  rcases glue_window_wide_int_cases habs with hn | hn | hn
  · subst hn
    have hm1 : w + ((-1 : ℤ) : ℂ) ∈ U := hwn
    have hrec : w + ((-1 : ℤ) : ℂ) + 1 = w := by ring
    have hm2 : w + ((-1 : ℤ) : ℂ) + 1 ∈ U := by rw [hrec]; exact hw
    have h := hR1 (w + ((-1 : ℤ) : ℂ)) hm1 hm2
    rw [hrec] at h
    rw [h]
    ring
  · subst hn
    simp
  · subst hn
    have hm : w + 1 ∈ U := by simpa using hwn
    have h := hR1 w hw hm
    simpa using h

open Set in
/-- The two-chart glue with a window of half-width `R1 ∈ (1/2, 1]` (so that the `ℤ`-saturation of
`Ulow ∪ Uhigh` covers all real parts) and *same-chart* compatibility supplied by `R (w+1) = R w + 1`.
The two charts have disjoint imaginary-part ranges, so the mixed `hcompat` is vacuous. -/
theorem glue_window_bool_wide {x₀ R1 Hband : ℝ} {Ulow Uhigh : Set ℂ} {Rlow Rhigh : ℂ → ℂ}
    (hR1lo : 1 / 2 < R1) (hR1hi : R1 ≤ 1)
    (hUlow : IsOpen Ulow) (hRlow : DifferentiableOn ℂ Rlow Ulow)
    (hRlow1 : ∀ w : ℂ, w ∈ Ulow → w + 1 ∈ Ulow → Rlow (w + 1) = Rlow w + 1)
    (hUhigh : IsOpen Uhigh) (hRhigh : DifferentiableOn ℂ Rhigh Uhigh)
    (hRhigh1 : ∀ w : ℂ, w ∈ Uhigh → w + 1 ∈ Uhigh → Rhigh (w + 1) = Rhigh w + 1)
    (hlow : Ulow ⊆ {w : ℂ | |w.re - x₀| < R1 ∧ |w.im| < Hband})
    (hhigh : Uhigh ⊆ {w : ℂ | |w.re - x₀| < R1 ∧ Hband < |w.im|}) :
    ∃ R' : ℂ → ℂ, ∃ DR : Set ℂ, IsOpen DR ∧ MandelDim.IsTEquivariantOn R' DR ∧
      DifferentiableOn ℂ R' DR ∧ (∀ w : ℂ, w ∈ Ulow → R' w = Rlow w) ∧
      (∀ w : ℂ, w ∈ Uhigh → R' w = Rhigh w) ∧
      DR = ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' (Ulow ∪ Uhigh) := by
  classical
  -- `1/2 < R1` is not needed for the gluing itself (only `R1 ≤ 1` enters the estimate below); it
  -- records that the window is wider than the critical `1/2`, which is what makes the `ℤ`-saturation
  -- of `Ulow ∪ Uhigh` cover all real parts -- the property the consumer uses.
  have _hR1wide : (1 / 2 : ℝ) < R1 := hR1lo
  -- the two-chart family, as an honest `Bool`-indexed family
  let U : Bool → Set ℂ := fun b => if b then Uhigh else Ulow
  let R : Bool → ℂ → ℂ := fun b => if b then Rhigh else Rlow
  have hUo : ∀ b : Bool, IsOpen (U b) := by
    intro b; cases b
    · exact hUlow
    · exact hUhigh
  have hRo : ∀ b : Bool, DifferentiableOn ℂ (R b) (U b) := by
    intro b; cases b
    · exact hRlow
    · exact hRhigh
  -- same-chart compatibility: the `+1`-relation plus the window of half-width `≤ 1`
  have hlowshift : ∀ (n : ℤ) (w : ℂ), w ∈ Ulow → w + (n : ℂ) ∈ Ulow →
      Rlow (w + (n : ℂ)) = Rlow w + (n : ℂ) :=
    glue_window_wide_shift_compat hR1hi hRlow1 (fun w hw => (hlow hw).1)
  have hhighshift : ∀ (n : ℤ) (w : ℂ), w ∈ Uhigh → w + (n : ℂ) ∈ Uhigh →
      Rhigh (w + (n : ℂ)) = Rhigh w + (n : ℂ) :=
    glue_window_wide_shift_compat hR1hi hRhigh1 (fun w hw => (hhigh hw).1)
  -- the gluing compatibility hypothesis of `tSat_glue`
  have hcompat : ∀ i j (n : ℤ) (w : ℂ), w ∈ U i → w + (n : ℂ) ∈ U j →
      R j (w + (n : ℂ)) = R i w + (n : ℂ) := by
    intro i j n w hi hj
    rcases eq_or_ne i j with rfl | hij
    · -- same chart
      cases i
      · exact hlowshift n w hi hj
      · exact hhighshift n w hi hj
    · -- different charts: disjoint imaginary-part ranges
      exfalso
      cases i <;> cases j
      · exact absurd rfl hij
      · have h1 : |w.im| < Hband := (hlow hi).2
        have h2 : Hband < |(w + (n : ℂ)).im| := (hhigh hj).2
        have him : (w + (n : ℂ)).im = w.im := by simp
        rw [him] at h2
        linarith
      · have h1 : Hband < |w.im| := (hhigh hi).2
        have h2 : |(w + (n : ℂ)).im| < Hband := (hlow hj).2
        have him : (w + (n : ℂ)).im = w.im := by simp
        rw [him] at h2
        linarith
      · exact absurd rfl hij
  obtain ⟨R', hopen, heq, hdiff, hagree⟩ := tSat_glue U R hUo hRo hcompat
  -- the `ℤ`-saturation of the `Bool`-family is the saturation of the union
  have hunion : (⋃ b : Bool, ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' U b)
      = ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' (Ulow ∪ Uhigh) := by
    dsimp only [U]
    ext z
    simp only [mem_iUnion, mem_image, Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true]
    constructor
    · rintro (⟨n, w, hw, hwz⟩ | ⟨n, w, hw, hwz⟩)
      · exact ⟨n, w, Or.inl hw, hwz⟩
      · exact ⟨n, w, Or.inr hw, hwz⟩
    · rintro ⟨n, w, hw, hwz⟩
      rcases hw with hw | hw
      · exact Or.inl ⟨n, w, hw, hwz⟩
      · exact Or.inr ⟨n, w, hw, hwz⟩
  refine ⟨R', ⋃ n : ℤ, (fun w => w + (n : ℂ)) '' (Ulow ∪ Uhigh), ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hunion]; exact hopen
  · rw [← hunion]; exact heq
  · rw [← hunion]; exact hdiff
  · intro w hw; exact hagree false w hw
  · intro w hw; exact hagree true w hw

end Work.Pert.pert2v2
