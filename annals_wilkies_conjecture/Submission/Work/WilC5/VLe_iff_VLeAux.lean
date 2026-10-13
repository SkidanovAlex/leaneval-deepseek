/-
  WilC5 — `VLe` and the "no absolute value" reformulation `VLeAux` agree.

  `Work.WilC5.VLe d z` says `|z| ≤ ((N : F) + 1) * |d|` for some `N`, while
  `Work.WilC5.VLeAux d z` only ever compares `z` with the two *signed* multiples `±(n·d)`.
  In an ordered field the two are equivalent because, for `c ≥ 0`,

    `max (c·d) (-(c·d)) = c·|d|`   and   `min (c·d) (-(c·d)) = -(c·|d|)`,

  so that "`z` is squeezed between `±(c·d)`" is exactly "`|z| ≤ c·|d|`" (the two
  disjunctions of `VLeAux` allow the squeeze to be realised with either sign of `d`).
  The implication `VLe → VLeAux` is proved by a case split on the sign of `d` instead of
  introducing `max`/`min` identities; the reverse implication then assembles `|z| ≤ c·|d|`
  from the two one-sided bounds.
-/
import Mathlib
import Submission.Work.WilC5.YVLeAuxDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

/-! ## The two halves of the equivalence -/

/-- **Squeezed between `±c·d` gives `|z| ≤ c·|d|`**: from the two one-sided bounds of
`VLeAux` (with an arbitrary nonnegative multiplier `c`) one obtains the absolute-value bound
defining `VLe`. -/
private theorem abs_le_mul_abs_of_bounds {F : Type} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (c : F) (hc : 0 ≤ c) (d z : F)
    (h1 : z ≤ c * d ∨ z ≤ -(c * d)) (h2 : c * d ≤ z ∨ -(c * d) ≤ z) :
    |z| ≤ c * |d| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- lower bound `-(c·|d|) ≤ z`
    rcases h2 with h | h
    · have hkey : -(c * |d|) ≤ c * d := by
        calc -(c * |d|) = c * (-|d|) := by ring
          _ ≤ c * d := mul_le_mul_of_nonneg_left (neg_abs_le d) hc
      linarith
    · have hkey : -(c * |d|) ≤ -(c * d) := by
        have hle : c * d ≤ c * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) hc
        linarith
      linarith
  · -- upper bound `z ≤ c·|d|`
    rcases h1 with h | h
    · have hle : c * d ≤ c * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) hc
      linarith
    · have hkey : -(c * d) ≤ c * |d| := by
        calc -(c * d) = c * (-d) := by ring
          _ ≤ c * |d| := mul_le_mul_of_nonneg_left (by linarith [neg_abs_le d]) hc
      linarith

/-- **`|z| ≤ c·|d|` gives the squeeze by `±c·d`**, for `c ≥ 0`.  Proved by cutting on the sign
of `d`, so that `|d|` is literally one of `d`, `-d`. -/
private theorem bounds_of_abs_le_mul_abs {F : Type} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (c : F) (hc : 0 ≤ c) (d z : F)
    (h : |z| ≤ c * |d|) :
    (z ≤ c * d ∨ z ≤ -(c * d)) ∧ (c * d ≤ z ∨ -(c * d) ≤ z) := by
  by_cases hd : (0 : F) ≤ d
  · rw [abs_of_nonneg hd] at h
    have hz := abs_le.mp h
    exact ⟨Or.inl hz.2, Or.inr hz.1⟩
  · have hdneg : d < 0 := lt_of_not_ge hd
    rw [abs_of_neg hdneg, mul_neg] at h
    have hz := abs_le.mp h
    refine ⟨Or.inr hz.2, Or.inl ?_⟩
    simpa using hz.1

/-! ## The requested equivalence -/

theorem VLe_iff_VLeAux {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (d z : F) : Work.WilC5.VLe d z ↔ Work.WilC5.VLeAux d z := by
  constructor
  · -- `VLe → VLeAux`: the multiplier `c = N + 1` is nonnegative, so `±c·d` squeeze `z`.
    rintro ⟨N, hN⟩
    have hcast : (((N + 1 : ℕ)) : F) = (N : F) + 1 := by push_cast; ring
    have hc : (0 : F) ≤ (N : F) + 1 := by positivity
    have key := bounds_of_abs_le_mul_abs ((N : F) + 1) hc d z hN
    refine ⟨N + 1, ?_⟩
    rw [hcast]
    exact key
  · -- `VLeAux → VLe`: the squeeze with multiplier `n` gives `|z| ≤ n·|d| ≤ ((n)+1)·|d|`.
    rintro ⟨n, h1, h2⟩
    refine ⟨n, ?_⟩
    have hc : (0 : F) ≤ (n : F) := Nat.cast_nonneg n
    have h := abs_le_mul_abs_of_bounds (n : F) hc d z h1 h2
    have hle : (n : F) * |d| ≤ ((n : F) + 1) * |d| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg d)
    exact le_trans h hle

end Work.WilC5
