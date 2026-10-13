import Mathlib
import Submission.Work.WilG5.Defs

set_option autoImplicit false

namespace Work.WilG5.Cell

/-- A `κ` cut out of `C × ℝ` by two `EReal`-valued bounds `a < · < b` whose every fibre
already lies in `[0,1]` has its fibres strictly inside `(0,1)`: were the last coordinate equal
to `0` (resp. `1`), some value slightly below (resp. above) the end `a` (resp. `b`) would
still satisfy the defining inequalities and hence violate the cube bound.

The only point to note is that `a (Fin.init x) < 0` (resp. `1 < b (Fin.init x)`) yields a *real*
`r` with `a (Fin.init x) < r < 0` (resp. `1 < r < b (Fin.init x)`), which is exactly
`EReal.lt_iff_exists_real_btwn`. -/
theorem fibre_strict {m : ℕ} {C : Set (Fin m → ℝ)} {a b : (Fin m → ℝ) → EReal}
    {κ : Set (Fin (m + 1) → ℝ)}
    (hκ : κ = {z : Fin (m + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < (((z (Fin.last m) : ℝ)) : EReal) ∧
      (((z (Fin.last m) : ℝ)) : EReal) < b (Fin.init z)})
    (hsub : κ ⊆ WilkiesDesign.cube01 (m + 1)) :
    ∀ x ∈ κ, (0 : ℝ) < x (Fin.last m) ∧ x (Fin.last m) < 1 := by
  intro x hx
  have hxmem : x ∈ {z : Fin (m + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < (((z (Fin.last m) : ℝ)) : EReal) ∧
      (((z (Fin.last m) : ℝ)) : EReal) < b (Fin.init z)} := hκ ▸ hx
  obtain ⟨hyC, ha, hb⟩ := hxmem
  have hcube : x (Fin.last m) ∈ Set.Icc (0 : ℝ) 1 := by
    have h' := hsub hx
    simp only [WilkiesDesign.cube01, Set.mem_ofPred_eq] at h'
    exact h' (Fin.last m)
  have hlow : (0 : ℝ) ≤ x (Fin.last m) := hcube.1
  have hup : x (Fin.last m) ≤ 1 := hcube.2
  -- every real strictly between the two ends lies in `[0,1]`
  have hmem : ∀ (r : ℝ), a (Fin.init x) < (r : EReal) → (r : EReal) < b (Fin.init x) →
      (0 : ℝ) ≤ r ∧ r ≤ 1 := by
    intro r har hrb
    have hz : Fin.snoc (Fin.init x) r ∈ κ := by
      rw [hκ]
      refine ⟨?_, ?_, ?_⟩
      · show Fin.init (Fin.snoc (Fin.init x) r) ∈ C
        rw [Fin.init_snoc]; exact hyC
      · show a (Fin.init (Fin.snoc (Fin.init x) r)) <
          (((Fin.snoc (Fin.init x) r) (Fin.last m) : ℝ) : EReal)
        rw [Fin.init_snoc, Fin.snoc_last]; exact har
      · show (((Fin.snoc (Fin.init x) r) (Fin.last m) : ℝ) : EReal) <
          b (Fin.init (Fin.snoc (Fin.init x) r))
        rw [Fin.init_snoc, Fin.snoc_last]; exact hrb
    have hz' := hsub hz
    simp only [WilkiesDesign.cube01, Set.mem_ofPred_eq] at hz'
    have h := hz' (Fin.last m)
    rw [Fin.snoc_last] at h
    exact h
  constructor
  · by_contra h
    push Not at h
    have h0 : x (Fin.last m) = 0 := le_antisymm h hlow
    have ha' : a (Fin.init x) < (0 : EReal) := by simpa [h0] using ha
    obtain ⟨r, har, hr0⟩ := EReal.lt_iff_exists_real_btwn.mp ha'
    have hrb : (r : EReal) < b (Fin.init x) :=
      lt_trans hr0 (by simpa [h0] using hb)
    have hge := (hmem r har hrb).1
    have hrneg : r < 0 := EReal.coe_lt_coe_iff.mp hr0
    linarith
  · by_contra h
    push Not at h
    have h1 : x (Fin.last m) = 1 := le_antisymm hup h
    have hb' : (1 : EReal) < b (Fin.init x) := by simpa [h1] using hb
    obtain ⟨r, h1r, hrb⟩ := EReal.lt_iff_exists_real_btwn.mp hb'
    have har : a (Fin.init x) < (r : EReal) :=
      lt_trans (by simpa [h1] using ha) h1r
    have hle := (hmem r har hrb).2
    have hone : (1 : ℝ) < r := EReal.coe_lt_coe_iff.mp h1r
    linarith

end Work.WilG5.Cell
