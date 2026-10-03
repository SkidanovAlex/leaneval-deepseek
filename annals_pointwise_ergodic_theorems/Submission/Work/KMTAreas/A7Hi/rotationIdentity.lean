import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral

/-!
# The window-phase rotation identity for the narrow cut

This file commits the **algebraic skeleton of the reduction** of
`Work.KMTAreas.A7Hi.fiberOpCutBoundUniform` to the *window-phase rotation bound*.

## The objects

For a finite set `A` of arithmetic frequencies and a family of *envelopes* `g : Circ → ℤ → ℂ`,

* `winSynth A g = ∑_{α ∈ A} e(-α ·) · g_α` is the **window synthesis**: a function whose spectrum
  is the union of the windows around the frequencies `α ∈ A` (the *reflected* characters are used
  because the cut's own symbol `∑_α per(m)(· - α)` pairs with `fourier (-j) α`; with this
  convention the `j`-dependence of an `(α,β)`-term is the *difference* `a_α - b_β`, which is what
  the `8δ`-separation controls -- using `e(+α·)` instead would make it the sum `a_α + b_β`, which
  separation does not control, cf. the review of `winCrossTsumEqZero`);
* `winRot A g j = ∑_{α ∈ A} e(-α j) · e(-α ·) · g_α` is the **per-window constant-phase
  rotation**: the `α`-window content of `winSynth A g`, multiplied by the constant phase `e(-α j)`.

## The identity (what is proved here, unconditionally)

`fiberOpSet A m 0 (winSynth A g) x` equals

  `∑'_j cw m j · (winRot A g j) (x - j)   +   ∑'_j cw m j · (the cross terms of the window pair)`

where the *cross terms* are the contributions of the pairs `(α, β)`, `α ≠ β`, i.e. the terms in
which the arithmetic character `e(-α j)` is paired with the *other* window's envelope `g_β`.

This is the exact place where the band limitation of the *input* enters: the input class of
`fiberOpCutBoundUniform` is the range of the `m'`-cut, so its spectrum lies in the windows, and the
**cross-term sum vanishes** (the `cw m`-convolution kills every frequency that is not at distance
`≤ δ` from one of the window centers, while `β - α` has modulus `≥ 8δ - 2δ > δ`); the cut then acts
on each window as the *modulation-removed* profile operator, which is precisely
`∑'_j cw m j · τ_j ∘ winRot ⋯`.  With the triangle inequality in `ℓᵖ(Vʳ)` and `∑'_j ‖cw m j‖ ≤ B`,
the whole cut bound therefore follows from the **window-phase rotation bound**

  `‖Vʳ(R_j u)‖_{ℓᵖ} ≤ C‖Vʳ(u)‖_{ℓᵖ}`  (uniformly in `j` and in the level `l`),

which is the remaining crux of `fiberOpCutBoundUniform` (see
`NOTES_A7Hi_fiberOpCutBoundUniform_SESSION.md`, §2).

The identity below is *unconditional* (no summability, no band hypothesis): it is the exact
pointwise-in-`j` splitting of the finite window sum, transported through the `j`-tsum by
`tsum_congr`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped BigOperators
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-- **The window synthesis** `∑_{α ∈ A} e(α ·) g_α` of a family of envelopes. -/
noncomputable def winSynth (A : Finset Circ) (g : Circ → ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑ α ∈ A, fourier (T := 1) (-x) α * g α x

/-- **The per-window constant-phase rotation**: the `α`-window content of the synthesis, with the
constant phase `e(-α j)` inserted in the `α`-th window.  This is the operator `R_j` of the crux. -/
noncomputable def winRot (A : Finset Circ) (g : Circ → ℤ → ℂ) (j : ℤ) : ℤ → ℂ :=
  fun y => ∑ α ∈ A, fourier (T := 1) (-j) α * (fourier (T := 1) (-y) α * g α y)

/-- The **cross-term summand** of the window pair `(α, β)` with `α ≠ β`: the term in which the
arithmetic character `e(-α j)` of the `α`-th window is paired with the envelope `g_β` of another
window.  On the band (the range of the `m'`-cut) these vanish after the `j`-sum, by the narrowness
of `m`; off the band they are the obstruction. -/
noncomputable def winCrossSummand (A : Finset Circ) (g : Circ → ℤ → ℂ) (j x : ℤ) : ℂ :=
  ∑ α ∈ A, ∑ β ∈ A.erase α,
    fourier (T := 1) (-j) α * (fourier (T := 1) (-(x - j)) β * g β (x - j))

/-- **The rotation identity (skeleton form, unconditional).**

For every finite frequency set `A`, every symbol `m` and every family of envelopes `g`,
the narrow cut of the window synthesis splits *exactly* as

  `fiberOpSet A m 0 (winSynth A g) x
     = ∑'_j cw m j · (winRot A g j) (x - j)  +  ∑'_j cw m j · winCrossSummand A g j x`.

The second sum is the "band" term: it is exactly the part of the identity that the hypothesis
`u n = fiberOp ρ l m' 0 (u n)` (spectrum in the windows) makes vanish, and its vanishing is the
analytic core of the crux (see the module docstring). -/
theorem fiberOpSet_winSynth_eq_rotation_add_cross (A : Finset Circ) (m : ℝ → ℂ)
    (g : Circ → ℤ → ℂ) (x : ℤ) :
    fiberOpSet A m 0 (winSynth A g) x
      = ∑' j : ℤ, (cw m j * winRot A g j (x - j) + cw m j * winCrossSummand A g j x) := by
  rw [fiberOpSet]
  refine tsum_congr fun j => ?_
  simp only [zero_sub, arithCharSet, winSynth, winRot, winCrossSummand]
  set F : Circ → ℂ := fun α => fourier (T := 1) (-j) α with hF
  set G : Circ → ℂ := fun β => fourier (T := 1) (-(x - j)) β * g β (x - j) with hG
  have key : (∑ α ∈ A, F α) * (∑ β ∈ A, G β)
      = (∑ α ∈ A, F α * G α) + ∑ α ∈ A, ∑ β ∈ A.erase α, F α * G β := by
    rw [Finset.sum_mul_sum]
    rw [show (∑ i ∈ A, ∑ j' ∈ A, F i * G j')
        = ∑ i ∈ A, (F i * G i + ∑ j' ∈ A.erase i, F i * G j') from
      Finset.sum_congr rfl fun i hi =>
        (Finset.add_sum_erase A (fun j' => F i * G j') hi).symm]
    rw [Finset.sum_add_distrib]
  calc (∑ α ∈ A, F α) * cw m j * ∑ β ∈ A, G β
      = cw m j * ((∑ α ∈ A, F α) * (∑ β ∈ A, G β)) := by ring
    _ = cw m j * ((∑ α ∈ A, F α * G α) + ∑ α ∈ A, ∑ β ∈ A.erase α, F α * G β) := by rw [key]
    _ = cw m j * (∑ α ∈ A, F α * G α) + cw m j * (∑ α ∈ A, ∑ β ∈ A.erase α, F α * G β) := by ring

/-- **The rotation identity**, given the vanishing of the cross-term sum.

If the cross terms vanish (which is what the band hypothesis `u n = fiberOp ρ l m' 0 (u n)` gives,
see the module docstring), the narrow cut of a window synthesis is *exactly* the
`cw m`-weighted sum of translates of the per-window phase rotation:

  `fiberOpSet A m 0 (winSynth A g) = ∑'_j cw m j · τ_j (winRot A g j)`.

This is the form in which the target `Work.KMTAreas.A7Hi.fiberOpCutBoundUniform` consumes the
identity: by the triangle inequality in `ℓᵖ(Vʳ)` the cut bound then follows from the
window-phase rotation bound `‖Vʳ(R_j u)‖_{ℓᵖ} ≤ C ‖Vʳ(u)‖_{ℓᵖ}` (uniform in `j` and in `l`),
together with `∑'_j ‖cw m j‖ ≤ B`. -/
theorem fiberOpSet_winSynth_eq_rotation_of_cross_zero (A : Finset Circ) (m : ℝ → ℂ)
    (g : Circ → ℤ → ℂ)
    (hcross : ∀ x : ℤ, (∑' j : ℤ, cw m j * winCrossSummand A g j x) = 0)
    (hsum₁ : ∀ x : ℤ, Summable (fun j : ℤ => cw m j * winRot A g j (x - j)))
    (hsum₂ : ∀ x : ℤ, Summable (fun j : ℤ => cw m j * winCrossSummand A g j x)) (x : ℤ) :
    fiberOpSet A m 0 (winSynth A g) x
      = ∑' j : ℤ, cw m j * winRot A g j (x - j) := by
  rw [fiberOpSet_winSynth_eq_rotation_add_cross A m g x,
    (hsum₁ x).tsum_add (hsum₂ x), hcross x, add_zero]

end

end Work.KMTAreas.A7Hi
