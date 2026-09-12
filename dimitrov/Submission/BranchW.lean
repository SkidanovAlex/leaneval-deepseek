import Mathlib
import Submission.Conjugates
import Submission.ConjPoly
import Submission.Minpoly
import Submission.Powers
import Submission.PowRev
import Submission.Rays
import Submission.HoloSqrt
import Submission.SqrtTaylor
import Submission.Continuation
import Submission.GOnCutPlane

/-!
# The w-plane holomorphic branch of `√G` for `G := R₂ · R₄`

This module assembles the analytic-continuation part of the engine for the
specific polynomial of the problem.  Fix the number field element `α` with
`P := minpoly ℤ α` (monic, degree `d`) and conjugate set
`S := conjugateValues α` (all elements nonzero because `α ≠ 0`).  Let

    G := Gpoly P := (pow2 P).reflect d * (pow4 P).reflect d ∈ ℤ[w]

and let `C := rootFinset S := {1/z², 1/z⁴ : z ∈ S}` (the roots of `G`).
Then the ray cut plane `U := Submission.Rays.cutPlane C` is an open simply
connected set with `0 ∈ U` containing a ball around `0`, on which `G` does
not vanish (`Submission.GOnCutPlane.Gpoly_ne_zero_on_cutPlane`).  Applying
`Submission.Continuation.sqrt_continuation` (whose hypotheses are exactly
these), with the formal square root `a` from
`Submission.PowRev.powRev_sqrt_integral` (whose convolution square is
`G.coeff`), yields the main analytic object of the engine:

> there is a holomorphic function `f : U → ℂ` with `f² = G` on `U`,
> `f 0 = 1`, and with Taylor coefficients at `0` equal to the *integer*
> sequence `a`.

After the change of variables `X = 1/w` this `f` is the holomorphic
continuation of the engine's integer Laurent series `f(1/X) = Σ aₖ X⁻ᵏ`
to the complement of the bounded star over `{z², z⁴}` -- the input of the
rationality theorem (Pólya / Bertrandias).

## Proof

* `P.Monic` (`Submission.Minpoly.minpoly_int_monic`), so
  `Submission.PowRev.powRev_sqrt_integral P hPmonic` provides
  `a : ℕ → ℤ`, `a 0 = 1`, with convolution square `(Gpoly P).coeff`.
* `rootFinset S` has no zero element: every `z ∈ S` is nonzero
  (`Submission.Dictionary.zero_not_mem_conjugateValues`), and inverses of
  nonzero complex numbers are nonzero.
* The five hypotheses of `sqrt_continuation` for `G := Gpoly P`,
  `U := cutPlane C`:
  - `G.coeff 0 = 1`: `Submission.GOnCutPlane.coeff_zero_Gpoly`;
  - `IsOpen U`: `Submission.Rays.isOpen_cutPlane`;
  - `IsSimplyConnected U`: `Submission.Rays.isSimplyConnected_cutPlane`;
  - `0 ∈ U`: `Submission.Rays.zero_mem_cutPlane`;
  - a ball around 0 inside U: `Submission.Rays.exists_ball_subset_cutPlane`;
  - `G` nonvanishing on `U`:
    `Submission.GOnCutPlane.Gpoly_ne_zero_on_cutPlane α hα hα0`.
* Apply `sqrt_continuation`; rearrange.

You may add helper definitions/lemmas.  Do NOT change the statement of
`exists_holomorphic_branch`.  No sorries may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial Real Topology

namespace Submission.BranchW

open Submission.Conjugates
open Submission.ConjPoly
open Submission.Powers
open Submission.Minpoly
open Submission.Rays
open Submission.SqrtTaylor
open Submission.GOnCutPlane

/-- The finite set of roots of `Gpoly`: `{1/z², 1/z⁴ : z ∈ S}`. -/
def rootFinset (S : Finset ℂ) : Finset ℂ :=
  (S.image (fun z : ℂ => (z ^ 2)⁻¹)) ∪ (S.image (fun z : ℂ => (z ^ 4)⁻¹))

/-- If every element of `S` is nonzero then so is every element of the root
finset (inverses of powers of nonzero complex numbers are nonzero). -/
lemma rootFinset_ne_zero {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0) :
    ∀ c ∈ rootFinset S, c ≠ 0 := by
  intro c hc
  dsimp [rootFinset] at hc
  rcases Finset.mem_union.mp hc with h | h
  · rcases Finset.mem_image.mp h with ⟨z, hz, rfl⟩
    exact inv_ne_zero (pow_ne_zero 2 (hS0 z hz))
  · rcases Finset.mem_image.mp h with ⟨z, hz, rfl⟩
    exact inv_ne_zero (pow_ne_zero 4 (hS0 z hz))

/-- **The w-plane branch.**  For a nonzero algebraic integer `α`, there is an
integer sequence `a` (the formal square root of `Gpoly (minpoly ℤ α)`) and a
holomorphic function `f` on the cut plane `cutPlane (rootFinset S)` (`S` the
conjugate set of `α`) with `f² = G`, `f 0 = 1`, and Taylor coefficients `a`. -/
theorem exists_holomorphic_branch {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    let P : ℤ[X] := minpoly ℤ α
    let S : Finset ℂ := conjugateValues α
    let C : Finset ℂ := rootFinset S
    ∃ a : ℕ → ℤ,
      a 0 = 1 ∧
        (∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) = (Gpoly P).coeff k) ∧
        ∃ f : ℂ → ℂ,
          DifferentiableOn ℂ f (cutPlane C) ∧
            (∀ z ∈ cutPlane C, f z ^ 2 = (Gpoly P).eval₂ (algebraMap ℤ ℂ) z) ∧
            f 0 = 1 ∧
            (∀ k : ℕ, taylorCoeff f k = (a k : ℂ)) := by
  classical
  -- Unfold the three `let` abbreviations of the statement.
  dsimp
  let C : Finset ℂ := rootFinset (conjugateValues α)
  -- The minimal polynomial is monic, so `PowRev.powRev_sqrt_integral` gives
  -- the integer sequence `a`, `a 0 = 1`, whose convolution square is the
  -- coefficient sequence of `Gpoly (minpoly ℤ α)`.
  have hPmonic : (minpoly ℤ α).Monic := minpoly_int_monic α hα
  rcases PowRev.powRev_sqrt_integral (minpoly ℤ α) hPmonic with ⟨a, ha0, ha⟩
  have ha' : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) =
      (Gpoly (minpoly ℤ α)).coeff k := by
    intro k
    simpa [Gpoly] using ha k
  -- Every conjugate of `α` is nonzero (α ≠ 0), hence every point of the
  -- root finset (the `{1/z², 1/z⁴}`) is nonzero as well.
  have hS0 : ∀ z ∈ conjugateValues α, z ≠ 0 := by
    intro z hz hz0
    exact (Submission.Dictionary.zero_not_mem_conjugateValues (α := α) hα0)
      (by simpa [hz0] using hz)
  have hC0 : ∀ c ∈ C, c ≠ 0 := by
    simpa [C] using (rootFinset_ne_zero (S := conjugateValues α) hS0)
  -- `Gpoly (minpoly ℤ α)` does not vanish on the cut plane of its roots.
  have hGne : ∀ z ∈ cutPlane C,
      (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) z ≠ 0 := by
    simpa [C, rootFinset] using (Gpoly_ne_zero_on_cutPlane (α := α) hα hα0)
  -- Assemble the analytic continuation on `cutPlane C` (open, simply
  -- connected, contains 0 and a ball around it) from `Continuation`.
  rcases (Continuation.sqrt_continuation
      (G := Gpoly (minpoly ℤ α))
      (hG0 := coeff_zero_Gpoly (minpoly ℤ α) hPmonic)
      (a := a) (ha0 := ha0) (ha := ha')
      (U := cutPlane C)
      (hUo := isOpen_cutPlane C)
      (hUsc := isSimplyConnected_cutPlane hC0)
      (hU0 := zero_mem_cutPlane hC0)
      (hball := exists_ball_subset_cutPlane hC0)
      (hGne := hGne)) with ⟨f, hfdiff, hfsq, hf0, htaylor⟩
  refine ⟨a, ha0, ?_⟩
  constructor
  · exact ha'
  · exact ⟨f, hfdiff, hfsq, hf0, htaylor⟩

end Submission.BranchW

end
