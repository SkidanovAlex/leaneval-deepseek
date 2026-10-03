import Mathlib
import Submission.Work.Peluse.Concat.Defs
import Submission.Work.Peluse.Ulower.boxNormPow_le_mass

/-!
# Objects for the reduction of `Work.Peluse.Concat.ConcatBridge`

This module isolates, sorry-free, the objects in terms of which the reduction of
`Work.Peluse.Concat.ConcatBridge` to the "dilation transfer"
`Work.Peluse.Concat.cdtTransferGen` is phrased.

* `Work.Peluse.Concat.dirFam c D ωOf d` — the direction family
  `i ↦ c·(d·ωOf i)[D]` attached to a difference tuple `d`;
* `Work.Peluse.Concat.Zbox c D N ωOf f d` — the level-`2^s-1` box norm of `f` with that family;
* `Work.Peluse.Concat.IsBad d` — `d` is degenerate when some non-empty sign pattern `ω` has
  `d·ω = 0` (then the corresponding direction set is the singleton `{0}` and the box norm
  collapses, so the dilation transfer cannot hold with a universal constant); `d = 0` is degenerate
  as well;
* `Work.Peluse.Concat.Zsum` — the sum of the `Zbox` over the differences `h - h'` of pairs of shift
  tuples, so that (`Work.Peluse.Concat.boxAvg_eq`) `boxAvg = M₁^{-2s}·Zsum`;
* `Work.Peluse.Concat.Lmass N f p` — the normalised `Lᵖ` mass `|S|⁻¹ ∑_x ‖f x‖ᵖ`.

The elementary bound `Zbox_le_lmass` records that for a `1`-bounded finitely supported `f` every
single `Zbox` is at most the `L¹` mass — that is the estimate that makes the degenerate tuples
harmless in the reduction (their total weight is `≲ M₁⁻¹`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-- The direction family `i ↦ c·(d·ωOf i)[D]` attached to the difference tuple `d`. -/
def dirFam {s : ℕ} (c : ℤ) (D : ℕ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)) (d : Fin s → ℤ) :
    Fin (2 ^ s - 1) → Finset ℤ :=
  fun i => Work.Peluse.arithIcc (c * dotZ (ωOf i) d) D

/-- The level-`2^s-1` box norm of `f` with the direction family of `d`.  This is the quantity that
the hypothesis of `ConcatBridge` averages over the pairs of shift tuples. -/
def Zbox {s : ℕ} (c : ℤ) (D N : ℕ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)) (f : ℤ → ℂ)
    (d : Fin s → ℤ) : ℝ :=
  Work.Peluse.boxNormPow (2 ^ s - 1) (dirFam c D ωOf d) (Work.Peluse.symIcc N) f

/-- `d` is *degenerate* when it is zero or some non-empty sign pattern kills it. -/
def IsBad {s : ℕ} (d : Fin s → ℤ) : Prop :=
  d = 0 ∨ ∃ ω : Fin s → Bool, ω ≠ 0 ∧ dotZ ω d = 0

/-- The sum of the `Zbox` over the differences `h - h'` of pairs of shift tuples. -/
def Zsum {s : ℕ} (c : ℤ) (D N M₁ : ℕ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool))
    (f : ℤ → ℂ) : ℝ :=
  ∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁, Zbox c D N ωOf f (tupSub h h')

/-- The normalised `Lᵖ` mass of `f` over the window `symIcc N`. -/
def Lmass (N : ℕ) (f : ℤ → ℂ) (p : ℕ) : ℝ :=
  (∑' x : ℤ, ‖f x‖ ^ p) * (((Work.Peluse.symIcc N).card : ℝ))⁻¹

/-- `boxAvg` is the normalised `Zsum`. -/
lemma boxAvg_eq {s : ℕ} (c : ℤ) (D N M₁ : ℕ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool))
    (f : ℤ → ℂ) :
    Work.Peluse.Concat.boxAvg s M₁ c ωOf D N f
      = ((M₁ : ℝ))⁻¹ ^ (2 * s) * Zsum c D N M₁ ωOf f := rfl

/-- Every `Zbox` is at most the `L¹` mass, for a `1`-bounded finitely supported `f`. -/
lemma Zbox_le_lmass {s : ℕ} (hs : 1 ≤ s) {c : ℤ} {D N : ℕ}
    {ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)} {f : ℤ → ℂ}
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfin : Work.Peluse.FinSuppZ f) (d : Fin s → ℤ) :
    Zbox c D N ωOf f d ≤ Lmass N f 1 := by
  have h1 : 1 ≤ 2 ^ s - 1 := by
    have : 2 ≤ 2 ^ s := by
      calc (2 : ℕ) = 2 ^ 1 := rfl
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega
  have h := Work.Peluse.Ulower.boxNormPow_le_mass h1 (dirFam c D ωOf d) (Work.Peluse.symIcc N) f
    hbd hfin
  simpa [Zbox, Lmass] using h

end

end Work.Peluse.Concat
