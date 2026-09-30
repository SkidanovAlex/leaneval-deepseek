import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Siegel/Bombieri coordinate sup, scaled by an algebraic integer `d`

For a number field `F`, a tuple `a : Fin n → F` and a tuple `b : Fin n → 𝓞 F` with
`(b j : F) = (d : F) * a j` for a nonzero algebraic integer `d`, the finite places' supremum
of the `v`-adic absolute values scales by `v d`:

`∏ᶠ v, (⨆ j, v (a j)) = (∏ᶠ v, v (d : F))⁻¹ * ∏ᶠ v, (⨆ j, v ((b j : 𝓞 F) : F))`.

The substance is the pointwise identity `⨆ j, v (b j) = v d * ⨆ j, v (a j)` (`v` is
multiplicative and `v d ≥ 0`, so multiplication by `v d` commutes with the finite supremum),
together with the fact that all three `finprod`s have finite multiplicative support. The
latter is the only non-formal input: `fun v ↦ v (a j)` has finite multiplicative support only
for `a j ≠ 0`, so the supremum has to be recognised as the maximum over the *nonzero* entries.
-/

namespace Work.BW

open NumberField

set_option linter.style.haveILetI false

/-- For a tuple `a : Fin n → F` with a nonzero entry, the function
`v ↦ ⨆ j, v (a j)` on the finite places has finite multiplicative support.

Indeed, away from finitely many places every nonzero `a j` is a `v`-adic unit and every zero
entry contributes `0 ≤ 1` to the supremum, so the supremum is `1` there. -/
theorem hasFiniteMulSupport_iSup_finitePlace {F : Type*} [Field F] [NumberField F] {n : ℕ}
    (a : Fin n → F) (h : ∃ j, a j ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NumberField.FinitePlace F => ⨆ j : Fin n, v (a j)) := by
  classical
  obtain ⟨j0, hj0⟩ := h
  haveI : Nonempty (Fin n) := ⟨j0⟩
  -- the set of indices carrying a nonzero entry
  set s : Finset (Fin n) := Finset.univ.filter (fun j => a j ≠ 0) with hs_def
  have hs : s.Nonempty := ⟨j0, by simp [hs_def, hj0]⟩
  have hmem : ∀ j : Fin n, a j ≠ 0 → j ∈ s := fun j hj => by simp [hs_def, hj]
  -- the full supremum is the maximum over the nonzero entries
  have hptSa : ∀ v : NumberField.FinitePlace F,
      (⨆ j : Fin n, v (a j)) = s.sup' hs (fun j => v (a j)) := by
    intro v
    refine le_antisymm ?_ ?_
    · refine ciSup_le (fun j => ?_)
      by_cases haj : a j = 0
      · rw [haj, map_zero]
        exact le_trans (AbsoluteValue.nonneg v.1 (a j0))
          (Finset.le_sup' (fun j => v (a j)) (hmem j0 hj0))
      · exact Finset.le_sup' (fun j => v (a j)) (hmem j haj)
    · refine Finset.sup'_le hs _ (fun j hj => ?_)
      exact le_ciSup (f := fun j : Fin n => v (a j)) (Set.finite_range _).bddAbove j
  have hf1 : Function.HasFiniteMulSupport
      (fun v : NumberField.FinitePlace F => s.sup' hs (fun j => v (a j))) := by
    refine Function.HasFiniteMulSupport.sup' s (fun j hj => ?_) hs
    exact NumberField.FinitePlace.hasFiniteMulSupport (by simpa [hs_def] using hj : a j ≠ 0)
  rw [show (fun v : NumberField.FinitePlace F => ⨆ j : Fin n, v (a j))
        = (fun v => s.sup' hs (fun j => v (a j))) from funext hptSa]
  exact hf1

theorem sieg2_finprod_iSup_scaling {F : Type*} [Field F] [NumberField F] {n : ℕ}
    (a : Fin n → F) (b : Fin n → NumberField.RingOfIntegers F)
    (d : NumberField.RingOfIntegers F) (hd : d ≠ 0) (h : ∃ j, a j ≠ 0)
    (hb : ∀ j, ((b j : NumberField.RingOfIntegers F) : F) = (d : F) * a j) :
    (∏ᶠ v : NumberField.FinitePlace F, (⨆ j : Fin n, v (a j))) =
      (∏ᶠ v : NumberField.FinitePlace F, v (d : F))⁻¹ *
        ∏ᶠ v : NumberField.FinitePlace F,
          (⨆ j : Fin n, v ((b j : NumberField.RingOfIntegers F) : F)) := by
  classical
  -- `d` is nonzero as an element of `F`
  have hdF : (d : F) ≠ 0 := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hd
  -- the three multiplicative supports are finite
  have hfSd : Function.HasFiniteMulSupport (fun v : NumberField.FinitePlace F => v (d : F)) :=
    NumberField.FinitePlace.hasFiniteMulSupport hdF
  have hfSa : Function.HasFiniteMulSupport
      (fun v : NumberField.FinitePlace F => ⨆ j : Fin n, v (a j)) :=
    hasFiniteMulSupport_iSup_finitePlace a h
  -- pointwise identity, from multiplicativity and `0 ≤ v d`
  have hpt : ∀ v : NumberField.FinitePlace F,
      (⨆ j : Fin n, v ((b j : NumberField.RingOfIntegers F) : F))
        = v (d : F) * ⨆ j : Fin n, v (a j) := by
    intro v
    have hmul : ∀ j : Fin n,
        v ((b j : NumberField.RingOfIntegers F) : F) = v (d : F) * v (a j) := by
      intro j; rw [hb j, map_mul]
    rw [show (⨆ j : Fin n, v ((b j : NumberField.RingOfIntegers F) : F))
          = (⨆ j : Fin n, v (d : F) * v (a j)) from iSup_congr hmul]
    exact (Real.mul_iSup_of_nonneg (AbsoluteValue.nonneg v.1 (d : F)) (fun j => v (a j))).symm
  -- the finprod of the `b`-supremum splits
  have hprod : (∏ᶠ v : NumberField.FinitePlace F,
        (⨆ j : Fin n, v ((b j : NumberField.RingOfIntegers F) : F)))
       = (∏ᶠ v : NumberField.FinitePlace F, v (d : F)) *
          (∏ᶠ v : NumberField.FinitePlace F, (⨆ j : Fin n, v (a j))) := by
    rw [show (∏ᶠ v : NumberField.FinitePlace F,
            (⨆ j : Fin n, v ((b j : NumberField.RingOfIntegers F) : F)))
          = ∏ᶠ v : NumberField.FinitePlace F, (v (d : F) * ⨆ j : Fin n, v (a j))
        from finprod_congr (fun v => hpt v)]
    exact finprod_mul_distrib hfSd hfSa
  have hSd_ne : (∏ᶠ v : NumberField.FinitePlace F, v (d : F)) ≠ 0 :=
    finprod_ne_zero (fun v => by
      intro hv
      exact hdF (eq_zero_of_map_eq_zero _ hv))
  rw [hprod, ← mul_assoc, inv_mul_cancel₀ hSd_ne, one_mul]

end Work.BW
