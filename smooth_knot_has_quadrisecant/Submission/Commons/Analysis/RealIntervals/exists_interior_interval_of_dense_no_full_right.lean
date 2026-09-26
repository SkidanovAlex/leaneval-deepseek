import Mathlib
import Submission.Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full

namespace Commons.Analysis.RealIntervals

/-- **Right-handed version of `exists_interior_interval_of_dense_no_full`**:
an open subset `S` of `ℝ` whose points are dense in every right neighbourhood
of a point `c < 1`, but which contains NO full strip `(c, b)` with `b ≤ 1`,
must contain an open interval `(a,b)` strictly inside `(c,1)` whose endpoints
are outside `S`.

This is the mirror image of
`exists_interior_interval_of_dense_no_full` under the involution `y ↦ 1 − y`,
which maps the interval `(c, 1)` onto `(0, 1 − c)` (reversing order). -/
theorem exists_interior_interval_of_dense_no_full_right {S : Set ℝ} (hSopen : IsOpen S) {c : ℝ}
    (hc1 : c < 1)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ S ∧ c < x ∧ x < c + ε)
    (hnoFull : ¬ ∃ b : ℝ, c < b ∧ b ≤ 1 ∧ Set.Ioo c b ⊆ S) :
    ∃ a b : ℝ, c < a ∧ a < b ∧ b < 1 ∧ Set.Ioo a b ⊆ S ∧ a ∉ S ∧ b ∉ S := by
  let T : Set ℝ := {y : ℝ | 1 - y ∈ S}
  let d : ℝ := 1 - c
  have hd0 : 0 < d := by
    dsimp [d]
    linarith
  have hTop : IsOpen T := by
    dsimp [T]
    -- T is the preimage of the open set S under the continuous map y ↦ 1 − y
    change IsOpen ((fun y : ℝ => 1 - y) ⁻¹' S)
    exact IsOpen.preimage (continuous_const.sub (continuous_id : Continuous (fun y : ℝ => y))) hSopen
  have hdenseT : ∀ ε : ℝ, 0 < ε → ∃ y : ℝ, y ∈ T ∧ d - ε < y ∧ y < d := by
    intro ε hε
    rcases hdense ε hε with ⟨x, hxS, hxc, hxlt⟩
    refine ⟨1 - x, ?_, ?_, ?_⟩
    · -- 1 - x ∈ T  ⟺  1 - (1 - x) = x ∈ S
      dsimp [T]
      have : 1 - (1 - x) = x := by ring
      simpa [this] using hxS
    · dsimp [d]
      linarith
    · dsimp [d]
      linarith
  have hnoFullT : ¬ ∃ b : ℝ, b < d ∧ 0 ≤ b ∧ Set.Ioo b d ⊆ T := by
    intro hbad
    rcases hbad with ⟨b, hbd, hb0, hsubT⟩
    apply hnoFull
    refine ⟨1 - b, ?_, ?_, ?_⟩
    · dsimp [d] at hbd
      linarith
    · linarith
    · intro x hx
      have hyT : 1 - x ∈ T := by
        apply hsubT
        rcases Set.mem_Ioo.mp hx with ⟨hxc, hxlt⟩
        dsimp [d] at hbd ⊢
        constructor <;> linarith
      have hxS' : 1 - (1 - x) ∈ S := by
        simpa [T] using hyT
      have : x ∈ S := by
        convert hxS' using 1
        ring
      exact this
  rcases exists_interior_interval_of_dense_no_full (S := T) hTop (c := d) hd0 hdenseT hnoFullT with
    ⟨a', b', ha'0, ha'b', hb'd, hsubT, ha'nT, hb'nT⟩
  refine ⟨1 - b', 1 - a', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [d] at hb'd
    linarith
  · linarith
  · linarith
  · intro x hx
    have hyT : 1 - x ∈ T := by
      apply hsubT
      rcases Set.mem_Ioo.mp hx with ⟨hx1, hx2⟩
      constructor <;> linarith
    have hxS' : 1 - (1 - x) ∈ S := by
      simpa [T] using hyT
    have : x ∈ S := by
      convert hxS' using 1
      ring
    exact this
  · -- 1 - b' ∉ S : a = 1 - b' lies in S iff b' lies in T
    exact fun hmem => hb'nT hmem
  · -- 1 - a' ∉ S : b = 1 - a' lies in S iff a' lies in T
    exact fun hmem => ha'nT hmem
