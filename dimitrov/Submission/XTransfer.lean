import Mathlib
import Submission.Rays
import Submission.BranchW

/-!
# Transfer of the branch to the `X`-plane by inversion

`Submission.BranchW.exists_holomorphic_branch` produces, in the `w`-plane,
a holomorphic function `f` on the cut plane `cutPlane C` (`C := rootFinset S`,
the set of roots `{1/z², 1/z⁴ : z ∈ S}`) with `f² = G`, `f 0 = 1`, and Taylor
coefficients `taylorCoeff f k = (a k : ℂ)` (integer sequence `a`).

The classical rationality theorems (Pólya / Bertrandias) apply to a function
holomorphic *outside a bounded compact set* with an integer Laurent series at
infinity.  That is the `X`-plane picture: put `X = 1/w`, so that

    g(X) := f(1/X).

The domain of `g` is the complement of the *bounded star*

    star S := ⋃_{z ∈ S} ( [0, z²] ∪ [0, z⁴] )

(the image of the rays under `w ↦ 1/w`):  for `X ≠ 0`,

    X ∉ star S   ⟺   1/X ∈ cutPlane C

(lemma `mem_star_compl_iff_inv_mem_cutPlane` below).  Moreover, for large
`|X|`, `1/X` lies in the Taylor ball of `f` at `0`, so

    g X = f (1/X) = ∑_k a k · X⁻ᵏ   (Laurent data at ∞, integer coefficients).

This module records the holomorphy transfer:

> if `f` is holomorphic on `cutPlane (rootFinset S)` then
> `g(X) := f (X⁻¹)` (with `g 0 := 0`) is holomorphic on `ℂ ∖ star S`.

(At a later stage the series identity `g X = Σ aₖ X⁻ᵏ` on the exterior is
recorded separately, using the Taylor identity from `BranchW`.)

## Definitions and lemmas

* `star S`: the union of the segments `[0, z²]` and `[0, z⁴]` over `z ∈ S`
  (`segment ℝ 0 (z ^ k)`).
* `mem_star_iff`: for `X ≠ 0`, membership in `star S` is equivalent to
  `X⁻¹ ∈ ⋃_{c ∈ rootFinset S} ray c` (i.e. to `X⁻¹ ∉ cutPlane C`).
* `holomorphicOn_star_compl_of_holomorphicOn_cutPlane`: the transfer.

## Notes for the proof of `holomorphicOn_star_compl_of_holomorphicOn_cutPlane`

Fix `X₀ ∉ star S` (so `X₀ ≠ 0` because `0 ∈ star S`).  By
`mem_star_compl_iff_inv_mem_cutPlane`, `X₀⁻¹ ∈ cutPlane C`, which is open
(`Rays.isOpen_cutPlane`); `f` is differentiable there.  The inversion map
`X ↦ X⁻¹` is differentiable at every nonzero point (`hasDerivAt_inv`); by the
chain rule `g` is differentiable at `X₀`.  (Piecewise value at `0` is
irrelevant since `0 ∉ (star S)ᶜ` is avoided -- actually `0 ∈ star S`, so the
domain `(star S)ᶜ` never contains `0`.)

You may add helper lemmas.  Do NOT change the statements of the declarations
below.  No sorries may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial Real Topology

namespace Submission.XTransfer

open Submission.Rays
open Submission.BranchW

/-- The bounded star `⋃_{z ∈ S} ([0, z²] ∪ [0, z⁴])` (in the `X`-plane). -/
def star (S : Finset ℂ) : Set ℂ :=
  {X : ℂ | ∃ z ∈ S, X ∈ segment ℝ 0 (z ^ 2) ∨ X ∈ segment ℝ 0 (z ^ 4)}

/-- The origin belongs to the star. -/
lemma zero_mem_star {S : Finset ℂ} (hSne : S.Nonempty) : (0 : ℂ) ∈ star S := by
  rcases hSne with ⟨z, hz⟩
  exact ⟨z, hz, Or.inl (left_mem_segment ℝ (0 : ℂ) (z ^ 2))⟩

/-- Membership in the segment `segment ℝ 0 c` is by real scalar multiples
`t • c` with `t ∈ [0, 1]`. -/
lemma mem_segment_zero_iff (c X : ℂ) :
    X ∈ segment ℝ 0 c ↔ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ X = t • c := by
  rw [segment_eq_image (𝕜 := ℝ) (x := (0 : ℂ)) (y := c)]
  constructor
  · rintro ⟨θ, hθ, hX⟩
    refine ⟨θ, hθ, ?_⟩
    calc
      X = (1 - θ) • (0 : ℂ) + θ • c := hX.symm
      _ = θ • c := by simp
  · rintro ⟨θ, hθ, hX⟩
    refine ⟨θ, hθ, ?_⟩
    calc
      (1 - θ) • (0 : ℂ) + θ • c = θ • c := by simp
      _ = X := hX.symm

/-- Each segment `segment ℝ 0 c` is closed (compact image of `[0,1]`). -/
lemma isClosed_segment_zero (c : ℂ) : IsClosed (segment ℝ 0 c) := by
  have himage : segment ℝ 0 c = (fun θ : ℝ => θ • c) '' Set.Icc (0 : ℝ) 1 := by
    rw [segment_eq_image (𝕜 := ℝ) (x := (0 : ℂ)) (y := c)]
    ext X
    constructor
    · rintro ⟨θ, hθ, hX⟩
      refine ⟨θ, hθ, ?_⟩
      change θ • c = X
      calc
        θ • c = (1 - θ) • (0 : ℂ) + θ • c := by simp
        _ = X := hX
    · rintro ⟨θ, hθ, hX⟩
      refine ⟨θ, hθ, ?_⟩
      change (1 - θ) • (0 : ℂ) + θ • c = X
      simpa using hX
  have hcont : Continuous (fun θ : ℝ => θ • c) := continuous_id.smul continuous_const
  rw [himage]
  exact (isCompact_Icc.image hcont).isClosed

/-- The star is closed (finite union of closed segments). -/
lemma isClosed_star (S : Finset ℂ) : IsClosed (star S) := by
  classical
  have hstar : star S = ⋃ z ∈ (S : Set ℂ), (segment ℝ 0 (z ^ 2) ∪ segment ℝ 0 (z ^ 4)) := by
    ext X
    simp [star]
  have hsegclosed : ∀ z ∈ (S : Set ℂ), IsClosed (segment ℝ 0 (z ^ 2) ∪ segment ℝ 0 (z ^ 4)) := by
    intro z hz
    exact (isClosed_segment_zero (z ^ 2)).union (isClosed_segment_zero (z ^ 4))
  rw [hstar]
  exact S.finite_toSet.isClosed_biUnion hsegclosed

/-- For `X ≠ 0`, `X` lies on the segment `[0, c]` iff `X⁻¹` lies on the ray
from `c⁻¹` (inversion turns a segment ending at `c` into the ray from `c⁻¹`). -/
lemma mem_segment_zero_iff_inv_mem_ray {X : ℂ} (hX : X ≠ 0) (c : ℂ) :
    X ∈ segment ℝ 0 c ↔ X⁻¹ ∈ ray c⁻¹ := by
  rw [mem_segment_zero_iff]
  constructor
  · rintro ⟨t, ht, hXeq⟩
    have ht_ne : t ≠ 0 := by
      intro ht0
      have : X = 0 := by
        rw [hXeq, ht0, zero_smul]
      exact hX this
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_ne)
    refine ⟨t⁻¹, (one_le_inv₀ htpos).2 ht.2, ?_⟩
    calc
      X⁻¹ = (t • c)⁻¹ := by rw [hXeq]
      _ = t⁻¹ • c⁻¹ := by rw [smul_inv₀]
  · rintro ⟨s, hs1, hseq⟩
    have hs_ne : s ≠ 0 := by
      intro hs0
      have : X⁻¹ = 0 := by
        rw [hseq, hs0, zero_smul]
      exact (inv_ne_zero hX) this
    have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    refine ⟨s⁻¹, ?_, ?_⟩
    · constructor
      · exact inv_nonneg.mpr (le_trans zero_le_one hs1)
      · simpa using ((inv_le_inv₀ (a := s) (b := (1 : ℝ)) hs_pos zero_lt_one).2 hs1)
    · calc
        X = (X⁻¹)⁻¹ := (inv_inv X).symm
        _ = (s • c⁻¹)⁻¹ := by rw [hseq]
        _ = s⁻¹ • (c⁻¹)⁻¹ := by rw [smul_inv₀]
        _ = s⁻¹ • c := by rw [inv_inv]

/-- The negated form of `mem_segment_zero_iff_inv_mem_ray`. -/
lemma not_mem_segment_zero_iff_inv_not_mem_ray {X : ℂ} (hX : X ≠ 0) (c : ℂ) :
    X ∉ segment ℝ 0 c ↔ X⁻¹ ∉ ray c⁻¹ := by
  constructor
  · intro h1 h2
    exact h1 ((mem_segment_zero_iff_inv_mem_ray hX c).2 h2)
  · intro h2 h1
    exact h2 ((mem_segment_zero_iff_inv_mem_ray hX c).1 h1)

/-- **Domain identity.**  For `X ≠ 0`, `X` avoids the star iff `1/X` lies in
the cut plane over the roots `rootFinset S`. -/
theorem mem_star_compl_iff_inv_mem_cutPlane {S : Finset ℂ} {X : ℂ} (hX : X ≠ 0) :
    X ∉ star S ↔ X⁻¹ ∈ cutPlane (rootFinset S) := by
  constructor
  · intro hXstar
    change ∀ c ∈ rootFinset S, X⁻¹ ∉ ray c
    intro c hc
    dsimp [rootFinset] at hc
    rcases Finset.mem_union.mp hc with hc2 | hc4
    · rcases Finset.mem_image.mp hc2 with ⟨z, hz, rfl⟩
      have hnotseg : X ∉ segment ℝ 0 (z ^ 2) := by
        intro hseg
        exact hXstar ⟨z, hz, Or.inl hseg⟩
      exact (not_mem_segment_zero_iff_inv_not_mem_ray hX (z ^ 2)).1 hnotseg
    · rcases Finset.mem_image.mp hc4 with ⟨z, hz, rfl⟩
      have hnotseg : X ∉ segment ℝ 0 (z ^ 4) := by
        intro hseg
        exact hXstar ⟨z, hz, Or.inr hseg⟩
      exact (not_mem_segment_zero_iff_inv_not_mem_ray hX (z ^ 4)).1 hnotseg
  · intro hcut
    change ∀ c ∈ rootFinset S, X⁻¹ ∉ ray c at hcut
    intro hXstar
    rcases hXstar with ⟨z, hz, hX2 | hX4⟩
    · have hray : X⁻¹ ∈ ray (z ^ 2)⁻¹ := (mem_segment_zero_iff_inv_mem_ray hX (z ^ 2)).1 hX2
      exact hcut ((z ^ 2)⁻¹) (by
        dsimp [rootFinset]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)) hray
    · have hray : X⁻¹ ∈ ray (z ^ 4)⁻¹ := (mem_segment_zero_iff_inv_mem_ray hX (z ^ 4)).1 hX4
      exact hcut ((z ^ 4)⁻¹) (by
        dsimp [rootFinset]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)) hray

/-- **Transfer.**  If `f` is holomorphic on the cut plane over `rootFinset S`,
then `g(X) := f (1/X)` is holomorphic on the complement of the star `star S`. -/
theorem holomorphicOn_star_compl_of_holomorphicOn_cutPlane {S : Finset ℂ}
    (hS : S.Nonempty) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (cutPlane (rootFinset S))) :
    DifferentiableOn ℂ (fun X : ℂ => if X = 0 then 0 else f (X⁻¹)) (star S)ᶜ := by
  intro X hX
  apply DifferentiableAt.differentiableWithinAt
  have hXne : X ≠ 0 := by
    intro hX0
    exact hX (by simpa [hX0] using (zero_mem_star (S := S) hS))
  have hXcut : X⁻¹ ∈ cutPlane (rootFinset S) :=
    (mem_star_compl_iff_inv_mem_cutPlane (S := S) hXne).1 hX
  have hfdiff : DifferentiableAt ℂ f (X⁻¹) :=
    hf.differentiableAt (IsOpen.mem_nhds (isOpen_cutPlane (rootFinset S)) hXcut)
  have hInvDiff : DifferentiableAt ℂ (fun y : ℂ => y⁻¹) X :=
    (hasDerivAt_inv hXne).differentiableAt
  have hcomp : DifferentiableAt ℂ (fun y : ℂ => f (y⁻¹)) X :=
    DifferentiableAt.comp X hfdiff hInvDiff
  have hF_eq : (fun y : ℂ => if y = 0 then 0 else f (y⁻¹)) =ᶠ[𝓝 X]
      (fun y : ℂ => f (y⁻¹)) := by
    filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hXne] with y hy
    simp [hy]
  exact hcomp.congr_of_eventuallyEq hF_eq

end Submission.XTransfer

end
