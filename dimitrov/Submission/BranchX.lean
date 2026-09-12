import Mathlib
import Submission.Conjugates
import Submission.Minpoly
import Submission.Powers
import Submission.BranchW
import Submission.GOnCutPlane
import Submission.XTransfer

/-!
# The X-plane branch: holomorphic off the star, integer Laurent data at ∞

`Submission.BranchW.exists_holomorphic_branch` gives, for a nonzero algebraic
integer `α`, the w-plane data: an integer sequence `a` (formal square root of
`Gpoly P`) and a holomorphic `f` on `cutPlane (rootFinset S)` with `f² = G`,
`f 0 = 1`, `taylorCoeff f k = (a k : ℂ)`.

`Submission.XTransfer.holomorphicOn_star_compl_of_holomorphicOn_cutPlane`
turns this into an X-plane function

    g X := if X = 0 then 0 else f (X⁻¹)

holomorphic on the complement of the bounded star `star S` over
`{z², z⁴ : z ∈ S}`.  This module assembles the two, and adds the *Laurent
data at infinity*: for `|X|` large (equivalently `w = X⁻¹` inside the Taylor
ball of `f` at `0`), the Taylor-series identity of `f`
(`Complex.hasSum_taylorSeries_on_ball`, using `taylorCoeff f k = (a k : ℂ)`)
becomes

    g X = f (X⁻¹) = ∑_k (a k : ℂ) · (X⁻¹)ᵏ = ∑_k (a k : ℂ) · X⁻ᵏ,

i.e. an integer-coefficient Laurent series at infinity (in `HasSum` form).
It also records the functional identity `g X ^ 2 = G(X⁻¹)` on the complement
of the star (transfer of `f² = G` through `X = 1/w`), which identifies the
singularities of `g` with the zeros of `G(1/·)`, i.e. with the star itself.

## Proof outline

1. Unpack `BranchW.exists_holomorphic_branch`:
   `⟨a, ha0, ha, f, hf, hfsq, hf0, htay⟩`.
2. `S.Nonempty`: `conjugateValues α` is the image of the (nonempty) type of
   embeddings `K →+* ℂ`.  `∀ z ∈ S, z ≠ 0`:
   `Submission.Dictionary.zero_not_mem_conjugateValues hα0`.
3. Apply `XTransfer.holomorphicOn_star_compl_of_holomorphicOn_cutPlane` with
   `hS := S.Nonempty` and `hf` to get differentiability of `g` on `(star S)ᶜ`.
4. The pointwise square identity: on `(star S)ᶜ` we have `X ≠ 0`
   (`0 ∈ star S`), `X⁻¹ ∈ cutPlane (rootFinset S)`
   (`mem_star_compl_iff_inv_mem_cutPlane`), and `g X = f (X⁻¹)`, so
   `g X ^ 2 = f (X⁻¹) ^ 2 = G.eval₂ φ (X⁻¹)` by `hfsq`.
5. Laurent data: `Rays.exists_ball_subset_cutPlane` gives `ρ > 0` with
   `ball 0 ρ ⊆ cutPlane (rootFinset S)`.  `f` is differentiable on that ball
   (restrict `hf`).  For `w ∈ ball 0 ρ`, `Complex.hasSum_taylorSeries_on_ball`
   gives `HasSum (fun k => taylorCoeff f k * w ^ k) (f w)`, which with
   `htay` (`taylorCoeff f k = (a k : ℂ)`) is
   `HasSum (fun k => (a k : ℂ) * w ^ k) (f w)`.  Take `R := ρ⁻¹`; for
   `R < ‖X‖` we have `w := X⁻¹` with `‖w‖ < ρ`, so `w ∈ ball 0 ρ`, and
   `g X = f w` (as `X ≠ 0`), giving the desired `HasSum` with `w ^ k`.

You may add helper lemmas.  Do NOT change the statement of
`exists_laurent_branch`.  No sorries may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial Real Topology

namespace Submission.BranchX

open Submission.Conjugates
open Submission.Minpoly
open Submission.Powers
open Submission.BranchW
open Submission.GOnCutPlane
open Submission.XTransfer
open Submission.Rays
open Submission.SqrtTaylor

/-- **X-plane branch.**  For a nonzero algebraic integer `α` there is an
integer sequence `a` and a holomorphic function `g` on the complement of the
bounded star `star S` (`S := conjugateValues α`) such that
`g X ^ 2 = G(X⁻¹)` on that complement, and for large `|X|`
`g X = ∑ₖ (a k) X⁻ᵏ` (integer Laurent series at infinity). -/
theorem exists_laurent_branch {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    let P : ℤ[X] := minpoly ℤ α
    let S : Finset ℂ := conjugateValues α
    ∃ a : ℕ → ℤ,
      a 0 = 1 ∧
        (∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) = (Gpoly P).coeff k) ∧
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g (Submission.XTransfer.star S)ᶜ ∧
            (∀ X ∈ (star S)ᶜ, g X ^ 2 = (Gpoly P).eval₂ (algebraMap ℤ ℂ) (X⁻¹)) ∧
            ∃ R : ℝ, 0 < R ∧
              ∀ X : ℂ, R < ‖X‖ →
                HasSum (fun k : ℕ => (a k : ℂ) * (X⁻¹) ^ k) (g X) := by
  classical
  dsimp
  rcases exists_holomorphic_branch (K := K) (α := α) hα hα0 with ⟨a, ha0, ha, f, hfdiff, hfsq, hf0, htay⟩
  refine ⟨a, ha0, ha, ?_⟩
  let g : ℂ → ℂ := fun X => if X = 0 then 0 else f (X⁻¹)
  refine ⟨g, ?_, ?_, ?_⟩
  · -- holomorphy on the complement of the star
    have hSne : (conjugateValues α).Nonempty := by
      dsimp [conjugateValues]
      exact Finset.image_nonempty.mpr Finset.univ_nonempty
    dsimp [g]
    exact XTransfer.holomorphicOn_star_compl_of_holomorphicOn_cutPlane (S := conjugateValues α) hSne hfdiff
  · -- square identity `g X ^ 2 = G(X⁻¹)` on the complement of the star
    have hSne : (conjugateValues α).Nonempty := by
      dsimp [conjugateValues]
      exact Finset.image_nonempty.mpr Finset.univ_nonempty
    intro X hX
    have hXne : X ≠ 0 := by
      intro hX0
      exact hX (by simpa [hX0] using (XTransfer.zero_mem_star (S := conjugateValues α) hSne))
    have hw : X⁻¹ ∈ cutPlane (rootFinset (conjugateValues α)) := by
      exact (XTransfer.mem_star_compl_iff_inv_mem_cutPlane (S := conjugateValues α) hXne).1 hX
    calc
      g X ^ 2 = (f (X⁻¹)) ^ 2 := by
        dsimp [g]
        simp [hXne]
      _ = (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) (X⁻¹) := hfsq (X⁻¹) hw
  · -- integer Laurent data at infinity
    have hS0 : ∀ z ∈ conjugateValues α, z ≠ 0 := by
      intro z hz hz0
      exact (Submission.Dictionary.zero_not_mem_conjugateValues (α := α) hα0) (by simpa [hz0] using hz)
    have hC0 : ∀ c ∈ rootFinset (conjugateValues α), c ≠ 0 := by
      exact rootFinset_ne_zero (S := conjugateValues α) hS0
    rcases Rays.exists_ball_subset_cutPlane (C := rootFinset (conjugateValues α)) hC0 with ⟨ρ, hρ, hρball⟩
    refine ⟨ρ⁻¹, inv_pos.mpr hρ, ?_⟩
    intro X hbig
    have hXpos : 0 < ‖X‖ := lt_trans (inv_pos.mpr hρ) hbig
    have hXne : X ≠ 0 := norm_pos_iff.mp hXpos
    let w : ℂ := X⁻¹
    have hnormX : ‖X‖⁻¹ < ρ := by
      have htmp : ‖X‖⁻¹ < (ρ⁻¹)⁻¹ := (inv_lt_inv₀ hXpos (inv_pos.mpr hρ)).mpr hbig
      simpa using htmp
    have hnormw : ‖w‖ < ρ := by
      dsimp [w]
      rwa [norm_inv]
    have hwball : w ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball]
      simpa using hnormw
    have hfball : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ) := hfdiff.mono hρball
    have hsum : HasSum (fun k : ℕ => (a k : ℂ) * w ^ k) (f w) := by
      have H0 := Complex.hasSum_taylorSeries_on_ball (f := f) hfball hwball
      refine HasSum.congr_fun H0 ?_
      intro k
      calc
        (a k : ℂ) * w ^ k = taylorCoeff f k * w ^ k := by rw [htay k]
        _ = ((↑k.factorial : ℂ)⁻¹ • (w - 0) ^ k • iteratedDeriv k f 0) := by
          unfold taylorCoeff
          simp [smul_eq_mul, sub_zero, mul_assoc, mul_comm, mul_left_comm]
    have hg : g X = f w := by
      dsimp [g, w]
      simp [hXne]
    simpa [w, hg] using hsum

end Submission.BranchX

end
