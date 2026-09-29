import Mathlib

namespace Work.TMC7Core.Scale

/-- Distance from a real `x` to the nearest integer, expressed through its fractional part:
`min (fract x) (1 - fract x) ∈ [0, 1/2]`. -/
private noncomputable def fracDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

/-- For an irrational `x` the distance to the nearest integer is strictly positive. -/
private lemma fracDist_pos {x : ℝ} (hx : Irrational x) : 0 < fracDist x := by
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x < 1 := Int.fract_lt_one x
  have hne : Int.fract x ≠ 0 := by
    intro h
    obtain ⟨z, hz⟩ := (Int.fract_eq_zero_iff).mp h
    refine hx ⟨(z : ℚ), ?_⟩
    rw [Rat.cast_intCast]
    exact hz
  unfold fracDist
  exact lt_min (lt_of_le_of_ne h0 (Ne.symm hne)) (by linarith)

/-- `fracDist x` really is a lower bound for the distance from `x` to any integer. -/
private lemma fracDist_le_abs_sub (x : ℝ) (a : ℤ) : fracDist x ≤ |x - (a:ℝ)| := by
  have hf_eq : Int.fract x = x - (⌊x⌋ : ℝ) := by
    have := Int.fract_add_floor x; linarith
  rcases le_or_gt a ⌊x⌋ with ha | ha
  · have hle' : (a:ℝ) ≤ (⌊x⌋:ℝ) := by exact_mod_cast ha
    have hnn : 0 ≤ x - (a:ℝ) := by linarith [Int.floor_le x]
    rw [abs_of_nonneg hnn]
    calc fracDist x ≤ Int.fract x := by unfold fracDist; exact min_le_left _ _
      _ = x - (⌊x⌋:ℝ) := hf_eq
      _ ≤ x - (a:ℝ) := by linarith
  · have hle' : (⌊x⌋:ℝ) + 1 ≤ (a:ℝ) := by
      have : ⌊x⌋ + 1 ≤ a := by omega
      exact_mod_cast this
    have hlt := Int.lt_floor_add_one x
    have hnp : x - (a:ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnp, neg_sub]
    calc fracDist x ≤ 1 - Int.fract x := by unfold fracDist; exact min_le_right _ _
      _ = (⌊x⌋:ℝ) + 1 - x := by rw [hf_eq]; ring
      _ ≤ (a:ℝ) - x := by linarith

/-- Rescaling: the integer-distance lower bound at `x * q` transfers to the rational
approximation `a / q` of `x`. -/
private lemma fracDist_div_le_abs (x : ℝ) (a : ℤ) {q : ℕ} (hq : 0 < q) :
    fracDist (x * (q:ℝ)) / (q:ℝ) ≤ |x - (a:ℝ)/(q:ℝ)| := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hfac : x * (q:ℝ) - (a:ℝ) = (q:ℝ) * (x - (a:ℝ)/(q:ℝ)) := by
    field_simp
  rw [div_le_iff₀ hqpos]
  calc fracDist (x * (q:ℝ)) ≤ |x * (q:ℝ) - (a:ℝ)| := fracDist_le_abs_sub _ _
    _ = (q:ℝ) * |x - (a:ℝ)/(q:ℝ)| := by rw [hfac, abs_mul, abs_of_pos hqpos]
    _ = |x - (a:ℝ)/(q:ℝ)| * (q:ℝ) := by ring

/-- The lower bound, obtained by induction on the denominator bound `Q`: the minimum over
`1 ≤ q ≤ Q` of the (positive) distances `fracDist (α q) / q`. -/
private lemma liouville_sep_aux (α : ℝ) (hα : Irrational α) :
    ∀ Q : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ Q →
      δ ≤ |α - (a : ℝ) / (q : ℝ)| := by
  intro Q
  induction Q with
  | zero =>
    exact ⟨1, one_pos, fun a q h1 h2 => by omega⟩
  | succ Q ih =>
    obtain ⟨δ, hδpos, hδ⟩ := ih
    have hirr : Irrational (α * ((Q + 1 : ℕ) : ℝ)) := by
      have h := hα.mul_intCast (m := ((Q + 1 : ℕ) : ℤ)) (by omega)
      simpa using h
    refine ⟨min δ (fracDist (α * ((Q + 1 : ℕ) : ℝ)) / ((Q + 1 : ℕ) : ℝ)),
      lt_min hδpos (div_pos (fracDist_pos hirr) (by positivity)), ?_⟩
    intro a q hq1 hq2
    rcases Nat.lt_or_ge q (Q + 1) with hlt | hge
    · have hle : q ≤ Q := by omega
      exact le_trans (min_le_left _ _) (hδ a q hq1 hle)
    · have hqe : q = Q + 1 := by omega
      subst hqe
      exact le_trans (min_le_right _ _) (fracDist_div_le_abs α a (Nat.succ_pos Q))

/-- Separation of an irrational from rationals with bounded denominator: the distance from `α`
to any `a/q` with `1 ≤ q ≤ Q₀` is bounded below by a positive constant. -/
theorem liouville_sep (α : ℝ) (hα : Irrational α) (Q₀ : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ Q₀ →
      δ ≤ |α - (a : ℝ) / (q : ℝ)| :=
  liouville_sep_aux α hα Q₀

end Work.TMC7Core.Scale
