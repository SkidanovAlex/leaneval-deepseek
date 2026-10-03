import Mathlib
import Submission.Work.Pert.tSat_glue
import Submission.Work.Pert.pert2v2.glue_window_bool_wide

/-!
# `Work.Pert.pert2v2.twoPieceROverlap` — the two-piece `R` from **overlapping** charts

`NOTES_pert2v2_session30.md` §9: `glue_window_bool_wide` and its family separate the two charts by
strict inequalities at one threshold, so exactly one line `{|Im| = H}` lies in neither chart, and
since `ℤ`-saturation preserves `|Im|` the glued `DR` misses that line.  Worse, **no** height-disjoint
pair of *open* charts can cover the band: an open set inside `{|Im| ≥ H}` lies in `{|Im| > H}`.  So
`PertData.DR_sub` (`K ∪ {y₁ ≤ |Im|} ⊆ DR`) is unreachable by a height-disjoint pair, and the charts
must **overlap**.

Here the charts overlap on the window band
`W = {|Re - x₀| < R1} ∩ {Hband < |Im|} ∩ {|Im| < Hband + 1}`, with `W ⊆ Ulow`, `W ⊆ Uhigh`, and the
pieces agreeing on `Ulow ∩ Uhigh` (`hcross` — in the design `pert2v2.Rlow_eq_retOf_level0`).  The
gluing is `Work.Pert.tSat_glue` (overlaps allowed); its cross compatibility is a three-case check
(`n ∈ {-1,0,1}` by the window `R1 ≤ 1`): `n = 0` is `hcross` directly, and `n = ±1` reduces to
`n = 0` by the same-chart shift because the base point then lies in `W`, hence in *both* charts.
-/

namespace Work.Pert.pert2v2

open Set

/-- **The two-piece return map from overlapping charts.** -/
theorem twoPieceR_overlap {x₀ R1 Hband : ℝ} {Ulow Uhigh : Set ℂ} {Rlow Rhigh : ℂ → ℂ}
    (hR1lo : 1 / 2 < R1) (hR1hi : R1 ≤ 1)
    (hUlow : IsOpen Ulow) (hRlow : DifferentiableOn ℂ Rlow Ulow)
    (hRlow1 : ∀ w : ℂ, w ∈ Ulow → w + 1 ∈ Ulow → Rlow (w + 1) = Rlow w + 1)
    (hUhigh : IsOpen Uhigh) (hRhigh : DifferentiableOn ℂ Rhigh Uhigh)
    (hRhigh1 : ∀ w : ℂ, w ∈ Uhigh → w + 1 ∈ Uhigh → Rhigh (w + 1) = Rhigh w + 1)
    (hwinLow : Ulow ⊆ {w : ℂ | |w.re - x₀| < R1 ∧ |w.im| < Hband + 1})
    (hwinHigh : Uhigh ⊆ {w : ℂ | |w.re - x₀| < R1 ∧ Hband < |w.im|})
    (hWlow : {w : ℂ | |w.re - x₀| < R1 ∧ Hband < |w.im| ∧ |w.im| < Hband + 1} ⊆ Ulow)
    (hWhigh : {w : ℂ | |w.re - x₀| < R1 ∧ Hband < |w.im| ∧ |w.im| < Hband + 1} ⊆ Uhigh)
    (hcross : ∀ w : ℂ, w ∈ Ulow → w ∈ Uhigh → Rhigh w = Rlow w) :
    ∃ R : ℂ → ℂ, ∃ DR : Set ℂ, IsOpen DR ∧ MandelDim.IsTEquivariantOn R DR ∧
      DifferentiableOn ℂ R DR ∧
      (∀ w : ℂ, w ∈ Ulow → R w = Rlow w) ∧
      (∀ w : ℂ, w ∈ Uhigh → R w = Rhigh w) ∧
      DR = ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' (Ulow ∪ Uhigh) := by
  classical
  let U : Bool → Set ℂ := fun b => if b then Uhigh else Ulow
  let R : Bool → ℂ → ℂ := fun b => if b then Rhigh else Rlow
  have hUo : ∀ b : Bool, IsOpen (U b) := by intro b; cases b <;> assumption
  have hRo : ∀ b : Bool, DifferentiableOn ℂ (R b) (U b) := by intro b; cases b <;> assumption
  have hlowshift : ∀ (n : ℤ) (w : ℂ), w ∈ Ulow → w + (n : ℂ) ∈ Ulow →
      Rlow (w + (n : ℂ)) = Rlow w + (n : ℂ) :=
    glue_window_wide_shift_compat hR1hi hRlow1 (fun w hw => (hwinLow hw).1)
  have hhighshift : ∀ (n : ℤ) (w : ℂ), w ∈ Uhigh → w + (n : ℂ) ∈ Uhigh →
      Rhigh (w + (n : ℂ)) = Rhigh w + (n : ℂ) :=
    glue_window_wide_shift_compat hR1hi hRhigh1 (fun w hw => (hwinHigh hw).1)
  -- a point of the overlap window lies in both charts
  have hmemW : ∀ w : ℂ, |w.re - x₀| < R1 → Hband < |w.im| → |w.im| < Hband + 1 →
      w ∈ Ulow ∧ w ∈ Uhigh := by
    intro w h3 h1 h2
    exact ⟨hWlow ⟨h3, h1, h2⟩, hWhigh ⟨h3, h1, h2⟩⟩
  -- the window forces `n ∈ {-1,0,1}`
  have hint : ∀ (n : ℤ) (w : ℂ), |w.re - x₀| < R1 → |(w + (n : ℂ)).re - x₀| < R1 →
      n = -1 ∨ n = 0 ∨ n = 1 := by
    intro n w h1 h2
    have hn : |((n : ℤ) : ℝ)| < 2 := by
      have hre : ((n : ℤ) : ℝ) = (w + (n : ℂ)).re - w.re := by simp
      rw [hre]
      have hsplit : (w + (n : ℂ)).re - w.re = ((w + (n : ℂ)).re - x₀) + (x₀ - w.re) := by ring
      rw [hsplit]
      calc |((w + (n : ℂ)).re - x₀) + (x₀ - w.re)|
          ≤ |(w + (n : ℂ)).re - x₀| + |x₀ - w.re| := abs_add_le _ _
        _ = |(w + (n : ℂ)).re - x₀| + |w.re - x₀| := by rw [abs_sub_comm x₀ w.re]
        _ < R1 + R1 := add_lt_add h2 h1
        _ ≤ 2 := by linarith
    exact glue_window_wide_int_cases hn
  -- cross compatibility, in the two orientations
  have hA : ∀ (n : ℤ) (w : ℂ), w ∈ Ulow → w + (n : ℂ) ∈ Uhigh →
      Rhigh (w + (n : ℂ)) = Rlow w + (n : ℂ) := by
    intro n w hw hw'
    have h1 : |w.re - x₀| < R1 := (hwinLow hw).1
    have h2 : |(w + (n : ℂ)).re - x₀| < R1 := (hwinHigh hw').1
    have him : (w + (n : ℂ)).im = w.im := by simp
    have hb : Hband < |w.im| := by have h := (hwinHigh hw').2; rwa [him] at h
    have hb' : |w.im| < Hband + 1 := (hwinLow hw).2
    have hW : w ∈ Ulow ∧ w ∈ Uhigh := hmemW w h1 hb hb'
    rcases hint n w h1 h2 with rfl | rfl | rfl
    · -- `n = -1`
      have hstep : Rhigh ((w + ((-1 : ℤ) : ℂ)) + 1) = Rhigh (w + ((-1 : ℤ) : ℂ)) + 1 :=
        hRhigh1 _ hw' (by simpa using hW.2)
      rw [show (w + ((-1 : ℤ) : ℂ)) + 1 = w from by push_cast; ring] at hstep
      have hgoal : Rhigh (w + ((-1 : ℤ) : ℂ)) = Rhigh w - 1 :=
        eq_sub_iff_add_eq.mpr hstep.symm
      rw [hgoal, hcross w hW.1 hW.2]
      push_cast; ring
    · -- `n = 0`
      have heq : Rhigh w = Rlow w := hcross w hW.1 (by simpa using hw')
      simpa using heq
    · -- `n = 1`
      have hstep : Rhigh (w + 1) = Rhigh w + 1 := hRhigh1 w hW.2 (by simpa using hw')
      push_cast
      rw [hstep, hcross w hW.1 hW.2]
  have hB : ∀ (n : ℤ) (w : ℂ), w ∈ Uhigh → w + (n : ℂ) ∈ Ulow →
      Rlow (w + (n : ℂ)) = Rhigh w + (n : ℂ) := by
    intro n w hw hw'
    have h1 : |w.re - x₀| < R1 := (hwinHigh hw).1
    have h2 : |(w + (n : ℂ)).re - x₀| < R1 := (hwinLow hw').1
    have him : (w + (n : ℂ)).im = w.im := by simp
    have hb : Hband < |w.im| := (hwinHigh hw).2
    have hb' : |w.im| < Hband + 1 := by have h := (hwinLow hw').2; rwa [him] at h
    have hW : w ∈ Ulow ∧ w ∈ Uhigh := hmemW w h1 hb hb'
    rcases hint n w h1 h2 with rfl | rfl | rfl
    · -- `n = -1`: same-chart shift of `Rlow` at `w - 1`
      have hstep : Rlow ((w + ((-1 : ℤ) : ℂ)) + 1) = Rlow (w + ((-1 : ℤ) : ℂ)) + 1 :=
        hRlow1 _ hw' (by simpa using hW.1)
      rw [show (w + ((-1 : ℤ) : ℂ)) + 1 = w from by push_cast; ring] at hstep
      have hgoal : Rlow (w + ((-1 : ℤ) : ℂ)) = Rlow w - 1 :=
        eq_sub_iff_add_eq.mpr hstep.symm
      rw [hgoal, hcross w hW.1 hW.2]
      push_cast; ring
    · -- `n = 0`
      have heq : Rhigh w = Rlow w := hcross w hW.1 hW.2
      simpa using heq.symm
    · -- `n = 1`
      have hstep : Rlow (w + 1) = Rlow w + 1 := hRlow1 w hW.1 (by simpa using hw')
      push_cast
      rw [hstep, hcross w hW.1 hW.2]
  have hcompat : ∀ i j (n : ℤ) (w : ℂ), w ∈ U i → w + (n : ℂ) ∈ U j →
      R j (w + (n : ℂ)) = R i w + (n : ℂ) := by
    intro i j n w hi hj
    rcases eq_or_ne i j with rfl | hij
    · cases i
      · exact hlowshift n w hi hj
      · exact hhighshift n w hi hj
    · cases i <;> cases j
      · exact absurd rfl hij
      · exact hA n w hi hj
      · exact hB n w hi hj
      · exact absurd rfl hij
  obtain ⟨R', hopen, heq, hdiff, hagree⟩ := tSat_glue U R hUo hRo hcompat
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
  exact ⟨R', ⋃ n : ℤ, (fun w : ℂ => w + (n : ℂ)) '' (Ulow ∪ Uhigh), by rw [← hunion]; exact hopen,
    by rw [← hunion]; exact heq, by rw [← hunion]; exact hdiff,
    fun w hw => hagree false w hw, fun w hw => hagree true w hw, rfl⟩

end Work.Pert.pert2v2
