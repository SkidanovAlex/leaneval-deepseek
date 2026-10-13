/-
  WilC4/ULPMExp : the small glue library shared by the slot lemma (`slot_bound`) and the
  assembly of `Work.WilC4.realULPM`.

  Contents:

  * `ExpSet E` — the (finite) set of *rational exponents* attached to a cluster set `E`:
    `0`, the `q` with `2^q ∈ E`, and the `q` with `2^q ∈ Mid E` (the last one is the exponent of
    a *constant* slot, on which the doubling ratio is constantly equal to a geometric midpoint of
    two consecutive cluster values).
  * `mid_pos`, `mid_finite`, `sq_mid_mem` — elementary facts about `Mid`.
  * `ULPMB_mono`, `ULPMStruct_mono` — both structural bundles are *antitone* in the breakpoint
    family `B` (an interval free of a larger `B` is free of the smaller one), so they may be
    transported to a larger breakpoint family.
  * `ratW_iff_valY` — `RatW` in terms of the partial value function `valY`; this is the bridge
    between the `RatW` vocabulary of `ulpm_Bx`/`dev_rate` and the function-level analysis of the
    telescoping.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMB

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr InD valY ratioY eq_valY valY_mem)

variable {k : ℕ}

/-! ## 1. Elementary facts about `Mid` -/

/-- Every element of `Mid E` is positive. -/
theorem mid_pos {E : Set ℝ} {m : ℝ} (hm : m ∈ Mid E) : 0 < m := by
  obtain ⟨ρ₁, -, ρ₂, -, -, -, -, -, hmpos⟩ := hm
  exact hmpos

/-- Every element of `Mid E` is the product of two consecutive positive elements of `E`, in the
squared form `m * m = ρ₁ * ρ₂`. -/
theorem sq_mid_mem {E : Set ℝ} {m : ℝ} (hm : m ∈ Mid E) :
    ∃ ρ₁ ∈ E, ∃ ρ₂ ∈ E, 0 < ρ₁ ∧ ρ₁ < ρ₂ ∧ m * m = ρ₁ * ρ₂ := by
  obtain ⟨ρ₁, h₁, ρ₂, h₂, hρ₁, hlt, -, hm2, -⟩ := hm
  exact ⟨ρ₁, h₁, ρ₂, h₂, hρ₁, hlt, hm2⟩

/-- `Mid E` is finite as soon as `E` is: it is contained in the image of `E × E` under
`(a, b) ↦ √(a b)`. -/
theorem mid_finite {E : Set ℝ} (hE : E.Finite) : (Mid E).Finite := by
  have h1 : (E ×ˢ E : Set (ℝ × ℝ)).Finite := hE.prod hE
  have h2 : ((fun p : ℝ × ℝ => p.1 * p.2) '' (E ×ˢ E : Set (ℝ × ℝ))).Finite := h1.image _
  have h3 : ((fun c : ℝ => Real.sqrt c) ''
      ((fun p : ℝ × ℝ => p.1 * p.2) '' (E ×ˢ E : Set (ℝ × ℝ)))).Finite := h2.image _
  refine h3.subset ?_
  intro m hm
  obtain ⟨ρ₁, h₁, ρ₂, h₂, -, -, -, hm2, hmpos⟩ := hm
  exact ⟨ρ₁ * ρ₂, ⟨(ρ₁, ρ₂), ⟨h₁, h₂⟩, rfl⟩,
    by change Real.sqrt (ρ₁ * ρ₂) = m
       rw [← hm2, ← sq, Real.sqrt_sq_eq_abs, abs_of_pos hmpos]⟩

/-! ## 2. The exponent set of `E` -/

/-- The set of rational exponents attached to a cluster set `E`: `0`, the `q : ℚ` with
`2 ^ q ∈ E`, and the `q : ℚ` with `2 ^ q ∈ Mid E`.

The first two come from the general slots (on which the doubling ratio is confined to one band of
`Mid E` and is close to its element of `E`), the last one from the *constant* slots, on which the
doubling ratio is constantly equal to a geometric midpoint of two consecutive cluster values. -/
def ExpSet (E : Set ℝ) : Set ℚ :=
  {q | q = 0 ∨ (∃ ρ ∈ E, 0 < ρ ∧ ρ = (2 : ℝ) ^ (q : ℝ)) ∨ (2 : ℝ) ^ (q : ℝ) ∈ Mid E}

theorem mem_expSet {E : Set ℝ} {q : ℚ} :
    q ∈ ExpSet E ↔
      q = 0 ∨ (∃ ρ ∈ E, 0 < ρ ∧ ρ = (2 : ℝ) ^ (q : ℝ)) ∨ (2 : ℝ) ^ (q : ℝ) ∈ Mid E :=
  Iff.rfl

/-- `ExpSet E` is contained in `{0}` together with the `q` whose `2`-th powers lie in `E` or in
`Mid E`. -/
theorem expSet_subset {E : Set ℝ} :
    ExpSet E ⊆ ({0} : Set ℚ) ∪ {q : ℚ | (2 : ℝ) ^ (q : ℝ) ∈ E} ∪
      {q : ℚ | (2 : ℝ) ^ (q : ℝ) ∈ Mid E} := by
  intro q hq
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hq ⊢
  rcases hq with h | h | h
  · exact Or.inl (Or.inl h)
  · obtain ⟨ρ, hρ, -, hρq⟩ := h
    exact Or.inl (Or.inr (hρq ▸ hρ))
  · exact Or.inr h

/-- `q ↦ 2 ^ q` is injective on `ℚ`. -/
theorem two_rpow_rat_injective : Function.Injective fun q : ℚ => (2 : ℝ) ^ (q : ℝ) := by
  intro q₁ q₂ h
  have h1 : Real.logb 2 ((2 : ℝ) ^ (((q₁ : ℚ) : ℝ))) = ((q₁ : ℚ) : ℝ) :=
    Real.logb_rpow (b := 2) (x := ((q₁ : ℚ) : ℝ)) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 ((2 : ℝ) ^ (((q₂ : ℚ) : ℝ))) = ((q₂ : ℚ) : ℝ) :=
    Real.logb_rpow (b := 2) (x := ((q₂ : ℚ) : ℝ)) (by norm_num) (by norm_num)
  have h' : (2 : ℝ) ^ (((q₁ : ℚ) : ℝ)) = (2 : ℝ) ^ (((q₂ : ℚ) : ℝ)) := h
  rw [h'] at h1
  exact_mod_cast (h1.symm.trans h2)

/-- `ExpSet E` is finite as soon as `E` is. -/
theorem expSet_finite {E : Set ℝ} (hE : E.Finite) : (ExpSet E).Finite := by
  have hmid := mid_finite hE
  have h2 : ({q : ℚ | (2 : ℝ) ^ (q : ℝ) ∈ E}).Finite :=
    hE.preimage (two_rpow_rat_injective.injOn.mono (Set.subset_univ _))
  have h3 : ({q : ℚ | (2 : ℝ) ^ (q : ℝ) ∈ Mid E}).Finite :=
    hmid.preimage (two_rpow_rat_injective.injOn.mono (Set.subset_univ _))
  have h4 : ((({0} : Set ℚ) ∪ {q : ℚ | (2 : ℝ) ^ (q : ℝ) ∈ E} ∪
      {q : ℚ | (2 : ℝ) ^ (q : ℝ) ∈ Mid E})).Finite :=
    ((Set.finite_singleton 0).union h2).union h3
  exact h4.subset expSet_subset

/-! ## 3. Both structural bundles are antitone in the breakpoint family -/

/-- `ULPMB` is antitone in `B`: an interval free of a larger breakpoint family is free of the
smaller one. -/
theorem ULPMB_mono {Y : Set (Fin (k + 2) → ℝ)} {B B' : Set (Fin (k + 1) → ℝ)}
    (hsub : B ⊆ B') (h : ULPMB Y B) : ULPMB Y B' := by
  refine ⟨fun c a b hab hfree => h.1 c a b hab fun x hx hxB => hfree x hx (hsub hxB),
    fun c a b hab hfree => h.2 c a b hab fun x hx hxB => hfree x hx (hsub hxB)⟩

/-- `ULPMStruct` is antitone in `B₀`. -/
theorem ULPMStruct_mono {Y : Set (Fin (k + 2) → ℝ)} {B B' : Set (Fin (k + 1) → ℝ)}
    (hsub : B ⊆ B') (h : ULPMStruct Y B) : ULPMStruct Y B' :=
  ⟨fun c a b hab hfree => h.1 c a b hab fun x hx hxB => hfree x hx (hsub hxB),
    fun c a b hab hfree => h.2 c a b hab fun x hx hxB => hfree x hx (hsub hxB)⟩

/-! ## 4. `RatW` in terms of the partial value function -/

/-- `w` is the doubling ratio of the fibre of `Y` at `(c, x)` iff `x` and `2x` both lie in the
domain with nonzero value and `w = valY (2x) / valY x`. -/
theorem ratW_iff_valY {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (c : Fin k → ℝ) (x w : ℝ) :
    RatW Y c x w ↔
      Gr Y c x (valY Y c x) ∧ Gr Y c (2 * x) (valY Y c (2 * x)) ∧ valY Y c x ≠ 0 ∧
        w = ratioY Y c x := by
  constructor
  · rintro ⟨y, y', hy, hy', hy0, hwy⟩
    have hyy : y = valY Y c x := eq_valY hfun hy
    have hyy' : y' = valY Y c (2 * x) := eq_valY hfun hy'
    rw [hyy] at hy hwy hy0
    rw [hyy'] at hy' hwy
    exact ⟨hy, hy', hy0, by rw [ratioY, eq_div_iff hy0]; exact hwy⟩
  · rintro ⟨hx, h2x, hne, hw⟩
    refine ⟨valY Y c x, valY Y c (2 * x), hx, h2x, hne, ?_⟩
    rw [hw, ratioY, div_mul_cancel₀ _ hne]

end Work.WilC4
