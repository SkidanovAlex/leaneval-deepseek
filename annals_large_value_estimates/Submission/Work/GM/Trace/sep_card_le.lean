import Mathlib
import Submission.Work.GM.Trace.Spart_defs

namespace Work.GM.Trace

/-- Two nonnegative reals whose floors agree are at distance `< 1`. -/
theorem floor_eq_abs_sub_lt_one (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (heq : ⌊a⌋₊ = ⌊b⌋₊) : |a - b| < 1 := by
  have ha1 : ((⌊a⌋₊ : ℕ) : ℝ) ≤ a := Nat.floor_le ha
  have hb1 : ((⌊b⌋₊ : ℕ) : ℝ) ≤ b := Nat.floor_le hb
  have ha2 : a < ((⌊a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
  have hb2 : b < ((⌊b⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one b
  have heq' : ((⌊a⌋₊ : ℕ) : ℝ) = ((⌊b⌋₊ : ℕ) : ℝ) := by exact_mod_cast heq
  rw [abs_lt]
  constructor <;> linarith

/-- A finite set of points in `[0,T]`, pairwise separated by at least `δ ≥ 1`,
has at most `T + 1` elements. -/
theorem sep_card_le (W : Finset ℝ) (T δ : ℝ) (hT : 0 ≤ T) (hδ : 1 ≤ δ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|) :
    (W.card : ℝ) ≤ T + 1 := by
  -- Distinct points of `W` have different floors, since they are at distance `≥ 1`.
  have hinj : Set.InjOn (fun t : ℝ => ⌊t⌋₊) (↑W : Set ℝ) := by
    intro t ht s hs heq
    by_contra hne
    have h1 : (1 : ℝ) ≤ |t - s| := le_trans hδ (hsep t ht s hs hne)
    have h2 : |t - s| < 1 := floor_eq_abs_sub_lt_one t s (hW t ht).1 (hW s hs).1 heq
    linarith
  have himage : (W.image (fun t : ℝ => ⌊t⌋₊)).card = W.card :=
    Finset.card_image_of_injOn hinj
  -- All floors lie in `{0, …, ⌊T⌋}`.
  have hsub : W.image (fun t : ℝ => ⌊t⌋₊) ⊆ Finset.range (⌊T⌋₊ + 1) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hW t ht).2))
  have hcard : W.card ≤ ⌊T⌋₊ + 1 := by
    calc W.card = (W.image (fun t : ℝ => ⌊t⌋₊)).card := himage.symm
      _ ≤ (Finset.range (⌊T⌋₊ + 1)).card := Finset.card_le_card hsub
      _ = ⌊T⌋₊ + 1 := Finset.card_range _
  calc (W.card : ℝ) ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊T⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ T + 1 := by have := Nat.floor_le hT; linarith

end Work.GM.Trace
