import Mathlib
import Submission.Work.LandLeaves.TypeGeometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Perturbation stability of cyclic betweenness

`Work.LandLeaves.ccBet a b x` says that the angle `x` lies on the counterclockwise arc from `a`
to `b` (angles mod `1`).  This file proves `Work.LandLeaves.ccBet_perturb`: if the three pairwise
differences of `a`, `b`, `x` keep distance `≥ δ` from the integers (where `3 * ϑ < δ`), then
moving `a`, `b`, `x` by at most `ϑ` each does not change the truth value of `ccBet`.

The proof is elementary.  Write `A = fract (x - a)`, `C = fract (b - x)`, `B = fract (b - a)`.
The hypotheses give `A, B, C ∈ [δ, 1 - δ]` with `δ > 0`; in particular all three lie in `(0,1)`.
Since `b - a = (x - a) + (b - x)`, we have `B = fract (A + C)`, and the two cases `A + C < 1`
resp. `A + C > 1` (the case `A + C = 1` being excluded by `B ≥ δ > 0`) give

* `ccBet a b x ↔ A + C < 1`,
* `|A - B| ≥ δ`.

Perturbing by `|e_i| ≤ ϑ` changes `A + C` only by `e₂ - e₁`, of modulus `≤ 2 * ϑ < δ`, so the sign
of `A + C - 1` — and hence the truth value of `ccBet` — is unchanged.
-/

noncomputable section

open Classical

namespace Work.LandLeaves

/-! ## Elementary arithmetic of `Int.fract` -/

/-- `Int.fract` of a sum only depends on the fractional parts. -/
private lemma fract_add_fract (u v : ℝ) :
    Int.fract (u + v) = Int.fract (Int.fract u + Int.fract v) := by
  have hu : u = Int.fract u + (⌊u⌋ : ℝ) := by
    have := Int.self_sub_floor u; linarith
  have hv : v = Int.fract v + (⌊v⌋ : ℝ) := by
    have := Int.self_sub_floor v; linarith
  have key : u + v = (Int.fract u + Int.fract v) + (((⌊u⌋ + ⌊v⌋ : ℤ)) : ℝ) := by
    have hc : (((⌊u⌋ + ⌊v⌋ : ℤ)) : ℝ) = (⌊u⌋ : ℝ) + (⌊v⌋ : ℝ) := by push_cast; ring
    rw [hc]; linarith
  rw [key, Int.fract_add_intCast]

/-- For `u ∈ [1,2)`, `Int.fract u = u - 1`. -/
private lemma fract_eq_sub_one {u : ℝ} (h1 : 1 ≤ u) (h2 : u < 2) : Int.fract u = u - 1 := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, 1, by ring⟩

/-- Shifting `u` by `t` when the result stays in `[0,1)` just adds `t` to `Int.fract u`. -/
private lemma fract_add_of_mem {u t : ℝ} (h1 : 0 ≤ Int.fract u + t) (h2 : Int.fract u + t < 1) :
    Int.fract (u + t) = Int.fract u + t := by
  rw [Int.fract_eq_iff]
  refine ⟨h1, h2, ⌊u⌋, ?_⟩
  have := Int.self_sub_floor u
  linarith

/-- If `u` keeps distance `≥ δ` from every integer, then `Int.fract u ∈ [δ, 1 - δ]`. -/
private lemma fract_bounds {u δ : ℝ} (h : ∀ m : ℤ, δ ≤ |u - m|) :
    δ ≤ Int.fract u ∧ δ ≤ 1 - Int.fract u := by
  have hu : u - (⌊u⌋ : ℝ) = Int.fract u := Int.self_sub_floor u
  constructor
  · have h1 := h ⌊u⌋
    rw [hu, abs_of_nonneg (Int.fract_nonneg u)] at h1
    exact h1
  · have h1 := h (⌊u⌋ + 1)
    have h2 : u - (((⌊u⌋ + 1 : ℤ)) : ℝ) = Int.fract u - 1 := by push_cast; linarith
    rw [h2, abs_of_nonpos (by linarith [Int.fract_lt_one u])] at h1
    linarith

/-- `|e - f| ≤ 2 * ϑ` when `|e| ≤ ϑ` and `|f| ≤ ϑ`. -/
private lemma abs_sub_le_two {e f ϑ : ℝ} (h1 : |e| ≤ ϑ) (h2 : |f| ≤ ϑ) :
    |e - f| ≤ 2 * ϑ := by
  calc |e - f| = |e + (-f)| := by ring_nf
    _ ≤ |e| + |-f| := abs_add_le _ _
    _ = |e| + |f| := by rw [abs_neg]
    _ ≤ 2 * ϑ := by linarith

/-! ## The combinatorial core -/

/-- If `fract (r - p)` and `fract (q - r)` are both strictly positive then the cyclic betweenness
of `p, q, r` is equivalent to those two fractional parts summing to less than `1`. -/
private lemma ccBet_iff_fract_add_lt_one {p q r : ℝ} (h1 : 0 < Int.fract (r - p))
    (h2 : 0 < Int.fract (q - r)) :
    ccBet p q r ↔ Int.fract (r - p) + Int.fract (q - r) < 1 := by
  have hB : Int.fract (q - p) = Int.fract (Int.fract (r - p) + Int.fract (q - r)) := by
    rw [← fract_add_fract (r - p) (q - r)]
    congr 1
    ring
  have hA0 : 0 < Int.fract (r - p) := h1
  have hC0 : 0 < Int.fract (q - r) := h2
  have hA1 : Int.fract (r - p) < 1 := Int.fract_lt_one _
  have hC1 : Int.fract (q - r) < 1 := Int.fract_lt_one _
  rw [ccBet, hB]
  rcases lt_trichotomy (Int.fract (r - p) + Int.fract (q - r)) 1 with h | h | h
  · have hf : Int.fract (Int.fract (r - p) + Int.fract (q - r))
        = Int.fract (r - p) + Int.fract (q - r) := Int.fract_eq_self.mpr ⟨by linarith, h⟩
    rw [hf]
    exact ⟨fun _ => h, fun _ => ⟨hA0, by linarith⟩⟩
  · have hf : Int.fract (Int.fract (r - p) + Int.fract (q - r)) = 0 := by
      rw [h]; exact Int.fract_one
    rw [hf]
    exact ⟨fun hh => absurd hh.2 (by linarith), fun _ => absurd h (by linarith)⟩
  · have hf : Int.fract (Int.fract (r - p) + Int.fract (q - r))
        = Int.fract (r - p) + Int.fract (q - r) - 1 :=
      fract_eq_sub_one (le_of_lt h) (by linarith)
    rw [hf]
    exact ⟨fun hh => absurd hh.2 (by linarith), fun _ => absurd h (by linarith)⟩

/-! ## The perturbation theorem -/

/-- **`ccBet` is stable under small perturbations of the three angles.**  If all three pairwise
differences `a - b`, `b - x`, `x - a` keep distance `≥ δ` from the integers and `3 * ϑ < δ`, then
moving the three angles by at most `ϑ` each does not change whether `x` lies on the
counterclockwise arc from `a` to `b`. -/
theorem ccBet_perturb {a b x : ℝ} {ϑ δ : ℝ} (hϑ : 0 ≤ ϑ) (h3 : 3 * ϑ < δ)
    (hab : ∀ m : ℤ, δ ≤ |a - b - m|) (hbx : ∀ m : ℤ, δ ≤ |b - x - m|)
    (hxa : ∀ m : ℤ, δ ≤ |x - a - m|) :
    ∀ e₁ e₂ e₃ : ℝ, |e₁| ≤ ϑ → |e₂| ≤ ϑ → |e₃| ≤ ϑ →
      (Work.LandLeaves.ccBet a b x ↔ Work.LandLeaves.ccBet (a + e₁) (b + e₂) (x + e₃)) := by
  have hδpos : 0 < δ := by linarith
  -- the same separation hypothesis, reindexed to the difference `b - a`
  have hab' : ∀ m : ℤ, δ ≤ |b - a - m| := fun m => by
    have h := hab (-m)
    have h2 : a - b - (((-m : ℤ)) : ℝ) = -(b - a - (m : ℝ)) := by push_cast; ring
    rw [h2, abs_neg] at h
    exact h
  obtain ⟨hA0, hA1⟩ := fract_bounds hxa
  obtain ⟨hB0, hB1⟩ := fract_bounds hab'
  obtain ⟨hC0, hC1⟩ := fract_bounds hbx
  -- `fract (b - a)` only depends on `fract (x - a)` and `fract (b - x)`
  have hBand : Int.fract (b - a) = Int.fract (Int.fract (x - a) + Int.fract (b - x)) := by
    rw [← fract_add_fract (x - a) (b - x)]
    congr 1
    ring
  -- consequently `fract (x - a) + fract (b - x)` keeps distance `≥ δ` from `1`
  have hAC : δ ≤ |Int.fract (x - a) + Int.fract (b - x) - 1| := by
    have hlt1 : Int.fract (x - a) < 1 := Int.fract_lt_one _
    have hlt2 : Int.fract (b - x) < 1 := Int.fract_lt_one _
    rcases lt_trichotomy (Int.fract (x - a) + Int.fract (b - x)) 1 with h | h | h
    · have hf : Int.fract (Int.fract (x - a) + Int.fract (b - x))
          = Int.fract (x - a) + Int.fract (b - x) := Int.fract_eq_self.mpr ⟨by linarith, h⟩
      rw [hf] at hBand
      have hge : 1 - (Int.fract (x - a) + Int.fract (b - x)) ≥ δ := by linarith
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hf : Int.fract (Int.fract (x - a) + Int.fract (b - x)) = 0 := by
        rw [h]; exact Int.fract_one
      rw [hf] at hBand
      have hz : Int.fract (x - a) + Int.fract (b - x) - 1 = 0 := by linarith
      rw [hz, abs_zero]
      linarith
    · have hf : Int.fract (Int.fract (x - a) + Int.fract (b - x))
          = Int.fract (x - a) + Int.fract (b - x) - 1 :=
        fract_eq_sub_one (le_of_lt h) (by linarith)
      rw [hf] at hBand
      have hge : Int.fract (x - a) + Int.fract (b - x) - 1 ≥ δ := by linarith
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hACdisp : (Int.fract (x - a) + Int.fract (b - x) - 1 ≤ -δ) ∨
      δ ≤ Int.fract (x - a) + Int.fract (b - x) - 1 := by
    rcases le_total (Int.fract (x - a) + Int.fract (b - x) - 1) 0 with hv | hv
    · left; have := abs_of_nonpos hv; linarith
    · right; have := abs_of_nonneg hv; linarith
  have hcc : ccBet a b x ↔ Int.fract (x - a) + Int.fract (b - x) < 1 :=
    ccBet_iff_fract_add_lt_one (by linarith) (by linarith)
  intro e₁ e₂ e₃ h1 h2 h3
  have he31 : |e₃ - e₁| ≤ 2 * ϑ := abs_sub_le_two h3 h1
  have he23 : |e₂ - e₃| ≤ 2 * ϑ := abs_sub_le_two h2 h3
  have he21 : |e₂ - e₁| ≤ 2 * ϑ := abs_sub_le_two h2 h1
  have he31a : -(2 * ϑ) ≤ e₃ - e₁ := (abs_le.mp he31).1
  have he31b : e₃ - e₁ ≤ 2 * ϑ := (abs_le.mp he31).2
  have he23a : -(2 * ϑ) ≤ e₂ - e₃ := (abs_le.mp he23).1
  have he23b : e₂ - e₃ ≤ 2 * ϑ := (abs_le.mp he23).2
  have he21a : -(2 * ϑ) ≤ e₂ - e₁ := (abs_le.mp he21).1
  have he21b : e₂ - e₁ ≤ 2 * ϑ := (abs_le.mp he21).2
  have hA' : Int.fract ((x + e₃) - (a + e₁)) = Int.fract (x - a) + (e₃ - e₁) := by
    rw [show (x + e₃) - (a + e₁) = (x - a) + (e₃ - e₁) by ring]
    exact fract_add_of_mem (by linarith) (by linarith)
  have hC' : Int.fract ((b + e₂) - (x + e₃)) = Int.fract (b - x) + (e₂ - e₃) := by
    rw [show (b + e₂) - (x + e₃) = (b - x) + (e₂ - e₃) by ring]
    exact fract_add_of_mem (by linarith) (by linarith)
  have hcc' : ccBet (a + e₁) (b + e₂) (x + e₃) ↔
      Int.fract ((x + e₃) - (a + e₁)) + Int.fract ((b + e₂) - (x + e₃)) < 1 :=
    ccBet_iff_fract_add_lt_one (by rw [hA']; linarith) (by rw [hC']; linarith)
  rw [hcc, hcc', hA', hC']
  have hring : Int.fract (x - a) + (e₃ - e₁) + (Int.fract (b - x) + (e₂ - e₃))
      = Int.fract (x - a) + Int.fract (b - x) + (e₂ - e₁) := by ring
  rw [hring]
  constructor
  · intro hlt
    rcases hACdisp with hh | hh
    · linarith
    · linarith
  · intro hlt
    rcases hACdisp with hh | hh
    · linarith
    · linarith

end Work.LandLeaves
