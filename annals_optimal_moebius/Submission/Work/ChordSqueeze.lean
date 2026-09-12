import Submission.Work.HeightSlope

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The 2-D chord squeeze (pure real algebra, GREEN)

THE central engine of the degenerate-height slope-continuity (the uniform
route of `session_status116`).  All leaf chords of the developable picture
that approach a covered height from the OUTER side of its flat frontier
chord lie strictly above (resp. below) that frontier chord in the open
strip; since their centreline heights converge to the frontier chord's
centre height, their SLOPES are squeezed to the frontier chord's slope.
No developable geometry is used here — only the elementary fact that a
chord at-or-above a fixed chord and through a nearby centreline height has
squeezed slope (evaluate the pointwise order at `x0 = 1/4` and
`x0 = 3/4`).

* `chordLine h m x` — the line `x1 = h + m·(x0 − 1/2)` (the strip chord
  through the centreline point `(1/2,h)` with slope `m`);
* `chord_above_slope_bound` — `|m − m₀| ≤ 4·|h − h₀|` for a chord
  at-or-above the reference chord `(h₀,m₀)` on `x0 ∈ (0,1)`;
* `slope_tendsto_of_chord_above` / `slope_tendsto_of_chord_below` — the
  squeeze versions used by the continuity layer.

Build: `lake build Submission.Work.ChordSqueeze` rc=0, zero sorry.
-/

namespace Submission

/-- The height of the strip chord through `(1/2,h)` of slope `m` at the
coordinate `x0`: `h + m·(x0 − 1/2)`. -/
noncomputable def chordLine (h m x : ℝ) : ℝ := h + m * (x - 1 / 2)

/-- A chord at-or-above the reference chord in the open strip has slope
squeezed by the centre-height gap: `|m − m₀| ≤ 4·|h − h₀|`. -/
lemma chord_above_slope_bound {h₀ m₀ h m : ℝ}
    (habove : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → chordLine h₀ m₀ x ≤ chordLine h m x) :
    |m - m₀| ≤ 4 * |h - h₀| := by
  have h₁ := habove (1 / 4 : ℝ) (by norm_num : (1 / 4 : ℝ) ∈ Set.Ioo 0 1)
  have h₃ := habove (3 / 4 : ℝ) (by norm_num : (3 / 4 : ℝ) ∈ Set.Ioo 0 1)
  have hup : m - m₀ ≤ 4 * (h - h₀) := by
    unfold chordLine at h₁
    ring_nf at h₁ ⊢
    nlinarith
  have hlo : m₀ - m ≤ 4 * (h - h₀) := by
    unfold chordLine at h₃
    ring_nf at h₃ ⊢
    nlinarith
  rw [abs_le]
  constructor
  · have hh : 4 * (h - h₀) ≤ 4 * |h - h₀| := by
      nlinarith [le_abs_self (h - h₀), abs_nonneg (h - h₀)]
    linarith
  · have hh : 4 * (h - h₀) ≤ 4 * |h - h₀| := by
      nlinarith [le_abs_self (h - h₀), abs_nonneg (h - h₀)]
    linarith

/-- A family of chords at-or-above the reference chord with centreline
heights `hₙ → h₀` has slopes `mₙ → m₀`. -/
theorem slope_tendsto_of_chord_above {h₀ m₀ : ℝ} {h m : ℕ → ℝ}
    (habove : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioo 0 1 → chordLine h₀ m₀ x ≤ chordLine (h n) (m n) x)
    (hh : Tendsto h atTop (𝓝 h₀)) : Tendsto m atTop (𝓝 m₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  rcases (Metric.tendsto_atTop.mp hh) (ε / 4) hε4 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hd : dist (h n) h₀ < ε / 4 := hN n hn
  have hd' : |h n - h₀| < ε / 4 := by
    simpa [Real.dist_eq] using hd
  have hb := chord_above_slope_bound (h₀ := h₀) (m₀ := m₀) (h := h n) (m := m n) (habove n)
  have hlt : |m n - m₀| < ε := by
    calc
      |m n - m₀| ≤ 4 * |h n - h₀| := hb
      _ < 4 * (ε / 4) := (mul_lt_mul_of_pos_left hd' (by norm_num : (0 : ℝ) < 4))
      _ = ε := by ring
  simpa [Real.dist_eq] using hlt

/-- Mirror: a family of chords at-or-BELOW the reference chord with
centreline heights `hₙ → h₀` has slopes `mₙ → m₀` (reflect through the
horizontal axis). -/
theorem slope_tendsto_of_chord_below {h₀ m₀ : ℝ} {h m : ℕ → ℝ}
    (hbelow : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioo 0 1 → chordLine (h n) (m n) x ≤ chordLine h₀ m₀ x)
    (hh : Tendsto h atTop (𝓝 h₀)) : Tendsto m atTop (𝓝 m₀) := by
  have habove : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Ioo 0 1 →
      chordLine (-h₀) (-m₀) x ≤ chordLine (-h n) (-m n) x := by
    intro n x hx
    have hb := hbelow n x hx
    unfold chordLine at hb ⊢
    ring_nf at hb ⊢
    nlinarith
  have hhneg : Tendsto (fun n : ℕ => -h n) atTop (𝓝 (-h₀)) := hh.neg
  have hm := slope_tendsto_of_chord_above (h₀ := -h₀) (m₀ := -m₀)
    (h := fun n : ℕ => -h n) (m := fun n : ℕ => -m n) habove hhneg
  simpa using hm.neg

end Submission
