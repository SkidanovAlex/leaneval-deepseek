import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.polysum_basic

/-!
# GM §6: the Heath–Brown pair-sum bound for the *shifted* Dirichlet polynomial

Guth–Maynard's Proposition 6.1 is fed by the "fully processed" Heath–Brown input
`Work.GM.S2.HBFull`, which bounds the pair sum

`Σ_{t₁,t₂ ∈ W} ‖Σ_{m ≤ X} a_m m^{i(t₁-t₂)}‖²`

for **arbitrary** coefficients `a` with `‖a m‖ ≤ 1`.  In the reflection argument of §6
the Dirichlet polynomial that actually appears carries the shift `2πξ` of the spectral
variable, i.e. one needs the same bound for

`Σ_{t₁,t₂} ‖PolySum Y (t₁ - t₂ + 2πξ)‖² ,  PolySum Y σ = Σ_{1 ≤ m ≤ ⌊Y⌋} m^{iσ}`.

This file deduces that shifted form from `HBFull` alone.  The point is that the shift is
*not* a perturbation of the frequencies but a unimodular coefficient:

`m^{i(t₁-t₂+2πξ)} = m^{i·2πξ} · m^{i(t₁-t₂)}`   for `m ≥ 1`,

and `a_m := m^{i·2πξ}` (zero for `m > Y`) satisfies `‖a_m‖ ≤ 1`.  So the lemma is an
application of `HBFull` with `X = Y` and these coefficients; no other input is used.

The identity `m^{i·2πξ} · m^{iσ} = m^{i(σ+2πξ)}` is `Complex.cpow_add`: the complex power
of the *positive* real `m` is additive in the exponent (`m ≠ 0`).
-/

open Complex Finset
open scoped BigOperators Topology

set_option autoImplicit false

namespace Work.GM.S2

/-- For `m ≥ 1` the phase shift is a coefficient: `m^{i·2πξ} · m^{iσ} = m^{i(σ + 2πξ)}`. -/
lemma cpow_shift_mul {m : ℕ} (hm : 0 < m) (σ ξ : ℝ) :
    (m : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * (m : ℂ) ^ (Complex.I * (σ : ℂ))
      = (m : ℂ) ^ (Complex.I * ((σ + 2 * Real.pi * ξ : ℝ) : ℂ)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Complex.cpow_add _ _ hm0]
  congr 1
  push_cast
  ring

/-- The shifted Dirichlet polynomial is the unshifted one with the unimodular coefficients
`m ↦ m^{i·2πξ}`. -/
lemma sum_shift_polysum {Y ξ t : ℝ} (hY : 0 ≤ Y) :
    (∑ m ∈ Finset.Icc 1 (Nat.floor Y),
        (if (m : ℝ) ≤ Y then (m : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) else 0)
          * (m : ℂ) ^ (Complex.I * (t : ℂ)))
      = PolySum Y (t + 2 * Real.pi * ξ) := by
  rw [PolySum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have hmY : (m : ℝ) ≤ Y :=
    le_trans (by exact_mod_cast hm2) (Nat.floor_le hY)
  rw [if_pos hmY]
  exact cpow_shift_mul hm1 t ξ

/-- The coefficient sequence `m ↦ m^{i·2πξ}` is bounded by `1` (it is unimodular for
`m ≥ 1`, and `0^z` is `0` or `1`). -/
lemma norm_shift_cpow_le (Y ξ : ℝ) : ∀ m : ℕ,
    ‖(if (m : ℝ) ≤ Y then (m : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) else 0)‖ ≤ 1 := by
  intro m
  by_cases h : (m : ℝ) ≤ Y
  · rw [if_pos h]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      by_cases hz : Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ) = 0
      · rw [hz, Complex.cpow_zero]
        norm_num
      · have h0 : (((0 : ℕ) : ℂ)) = 0 := by norm_num
        rw [h0, Complex.zero_cpow hz]
        norm_num
    · simpa using (norm_cpow_unimodular hmpos (2 * Real.pi * ξ)).le
  · rw [if_neg h]
    norm_num

/-- **Guth–Maynard §6, `k = 4`, shifted form.**  Assuming the fully processed
Heath–Brown input `HBFull`, the pair sum of the phase-shifted Dirichlet polynomials
`PolySum Y (t i - t j + 2πξ)` obeys the same bound as the unshifted one with `X = Y`. -/
theorem hb_poly_pair_sum (hhb : Work.GM.S2.HBFull) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (T Y : ℝ), 1 ≤ T → T ≤ (N : ℝ) ^ 2 → 1 ≤ Y → Y ≤ (N : ℝ) →
      ∀ (ξ : ℝ) (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∑ i : Fin R, ∑ j : Fin R,
            ‖Work.GM.S2.PolySum Y (t i - t j + 2 * Real.pi * ξ)‖ ^ 2)
          ≤ C * (N : ℝ) ^ δ * ((R : ℝ) ^ 2 * Y + (R : ℝ) ^ ((7 : ℝ) / 4) * Y ^ 2
              + (R : ℝ) ^ ((29 : ℝ) / 16) * T ^ ((1 : ℝ) / 8) * Y) := by
  intro δ hδ
  obtain ⟨C, hC, N₀, hN₀⟩ := hhb δ hδ
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN T Y hT1 hTN hY1 hYN ξ R t htI htsep
  have hY0 : 0 ≤ Y := le_trans zero_le_one hY1
  set a : ℕ → ℂ :=
    fun m => if (m : ℝ) ≤ Y then (m : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) else 0
    with ha
  have ha_norm : ∀ m, ‖a m‖ ≤ 1 := fun m => norm_shift_cpow_le Y ξ m
  have ha_zero : ∀ m : ℕ, Y < (m : ℝ) → a m = 0 := by
    intro m hm
    show (if (m : ℝ) ≤ Y then (m : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) else 0) = 0
    exact if_neg (not_le.mpr hm)
  have hbound := hN₀ N hN T Y hT1 hTN hY1 hYN R t htI htsep a ha_norm ha_zero
  have hinner : ∀ i j : Fin R,
      (∑ m ∈ Finset.Icc 1 (Nat.floor Y),
          a m * (m : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ)))
        = PolySum Y (t i - t j + 2 * Real.pi * ξ) := by
    intro i j
    show (∑ m ∈ Finset.Icc 1 (Nat.floor Y),
        (if (m : ℝ) ≤ Y then (m : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) else 0)
          * (m : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ)))
      = PolySum Y (t i - t j + 2 * Real.pi * ξ)
    exact sum_shift_polysum hY0
  have hsum : (∑ i : Fin R, ∑ j : Fin R,
          ‖PolySum Y (t i - t j + 2 * Real.pi * ξ)‖ ^ 2)
      = (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y),
              a m * (m : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ))‖ ^ 2) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hinner i j]
  rw [hsum]
  exact hbound

end Work.GM.S2
