import Mathlib

/-!
# Straightening an arc: the elementary core

`CutPush/NOTES_arc_flattening_ROUTE.md` §2–§3 records the one geometric input of the collar
trivialisation of `Work.Whitney.CutPush.hasFingerData_holds`: **the finger of a smooth arc can be
flattened into a plane**, and the only non-elementary step of the standard proof is *arc
unknotting* — every smooth embedded arc in `ℝ^m` (large codimension) is isotopic to a straight
segment.

This file isolates the *elementary* half of that step, which is all the rest of the construction
needs once a good direction is in hand:

> **`Work.Whitney.CutPush.straighteningFamily`.**  Let `c : ℝ → ℝ^m`, let `v ≠ 0` be a direction
> such that **no chord** of `c` restricted to `[0,1]` is parallel to `v` (`ChordFree`), and let
> `Λ ≠ 0`.  Then the explicit family
> `Φ lam t = lam • c t + (1 - lam) • (c 0 + (Λ * t) • v)`
> has `Φ 1 = c`, `Φ 0` = the straight segment `t ↦ c 0 + (Λ * t) • v`, and **every** member
> `Φ lam` is injective on `Icc 0 1`.

The proof is the one-line computation `Φ lam t - Φ lam t' = lam • (c t - c t') + ((1-lam) * (Λ * (t-t'))) • v`:
a collision of `Φ lam` at `lam ≠ 0` exhibits `c t - c t'` as a multiple of `v`, which `ChordFree`
forbids; and `lam = 0` is the segment, whose injectivity is `v ≠ 0`.

Two consequences are recorded:

* `chordFree_injOn` — `ChordFree` *implies* that `c` is injective (take `α = 0`), so it is the only
  injectivity hypothesis the family needs;
* `chordFree_of_image_subset_subspace` — the *cheap source of a chord-free direction*: if the arc's
  image lies in a linear subspace `U` and `v ∉ U`, then `v` is chord-free.  In particular **every
  arc whose image lies in a proper subspace `U ⊊ ℝ^m` can be straightened** (take any `v ∉ U`); this
  is the case the collar construction reaches whenever the arc can be chosen inside the preimage of
  a small-codimension plane.

What is *not* in this file (and is the honest remaining input of the flattening) is

* the existence of a chord-free direction for an *arbitrary* smooth embedded arc in `ℝ^m`,
  `m ≥ 3` — true, but its standard proof uses Sard's theorem (the chord-direction map is a smooth
  map from a `2`-dimensional domain into `S^{m-1}`, `m - 1 ≥ 3`, so its image has measure zero);
  see `CutPush/NOTES_arc_flattening_ROUTE.md`;
* the realisation of the family as a *global ambient isotopy* of `ℝ^{2n}` (velocity-field extension
  along the tube and flow), and the subsequent tube/framing straightening.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

variable {m : ℕ}

/-- **The chord-free direction condition.**  No chord of the arc `c` over `[0,1]` is parallel to
`v`: for `t ≠ t'` in `[0,1]` and every real `α` one has `c t - c t' ≠ α • v`.

Taking `α = 0` this forces `c` to be injective on `[0,1]` (`chordFree_injOn`), so `ChordFree` is the
*single* hypothesis the straightening family needs. -/
def ChordFree (c : ℝ → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1, t ≠ t' →
    ∀ α : ℝ, c t - c t' ≠ α • v

/-- **A chord-free direction makes the arc injective.** -/
theorem chordFree_injOn {c : ℝ → EuclideanSpace ℝ (Fin m)} {v : EuclideanSpace ℝ (Fin m)}
    (h : ChordFree c v) : Set.InjOn c (Set.Icc (0 : ℝ) 1) := by
  intro t ht t' ht' hcon
  by_contra hne
  exact h t ht t' ht' hne 0 (by rw [hcon, sub_self, zero_smul])

/-- **The straightening family.**  `Φ lam t = lam • c t + (1 - lam) • (c 0 + (Λ * t) • v)`: the
convex combination (in `lam`) of the arc `c` and the straight segment in direction `v` starting at
`c 0`. -/
noncomputable def straighteningFamily (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) : ℝ → ℝ → EuclideanSpace ℝ (Fin m) :=
  fun lam t => lam • c t + (1 - lam) • (c 0 + (Λ * t) • v)

/-- **The difference formula for the straightening family.** -/
theorem straighteningFamily_sub {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (v : EuclideanSpace ℝ (Fin m)) (Λ lam t t' : ℝ) :
    straighteningFamily c v Λ lam t - straighteningFamily c v Λ lam t'
      = lam • (c t - c t') + ((1 - lam) * (Λ * (t - t'))) • v := by
  simp only [straighteningFamily, smul_add, smul_sub, smul_smul]
  module

/-- **Every member of the straightening family is injective.**  This is the content of the file: for
`lam ≠ 0` a collision exhibits `c t - c t'` as a multiple of `v`, which `ChordFree` forbids; and
`lam = 0` is the straight segment. -/
theorem straighteningFamily_injOn {c : ℝ → EuclideanSpace ℝ (Fin m)}
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) (hcf : ChordFree c v) (Λ : ℝ) (hΛ : Λ ≠ 0)
    (lam : ℝ) : Set.InjOn (straighteningFamily c v Λ lam) (Set.Icc (0 : ℝ) 1) := by
  intro t ht t' ht' hcon
  by_cases hlam : lam = 0
  · -- the straight segment
    subst hlam
    have h1 : (Λ * t) • v = (Λ * t') • v := by
      have h := hcon
      simp only [straighteningFamily, zero_smul, sub_zero, one_smul, zero_add] at h
      exact add_left_cancel h
    have h2 : (Λ * (t - t')) • v = 0 := by
      rw [mul_sub, sub_smul, h1, sub_self]
    have h3 : Λ * (t - t') = 0 := (smul_eq_zero.mp h2).resolve_right hv
    have h4 : t - t' = 0 := (mul_eq_zero.mp h3).resolve_left hΛ
    linarith
  · -- a collision gives a chord parallel to `v`
    by_contra hne
    have hdiff := straighteningFamily_sub (c := c) v Λ lam t t'
    rw [hcon, sub_self] at hdiff
    have hkey : lam • (c t - c t') = (-((1 - lam) * (Λ * (t - t')))) • v := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hdiff.symm
    have hchord : c t - c t' = (lam⁻¹ * (-((1 - lam) * (Λ * (t - t'))))) • v := by
      have h3 : c t - c t' = lam⁻¹ • (lam • (c t - c t')) := by
        rw [smul_smul, inv_mul_cancel₀ hlam, one_smul]
      rw [h3, hkey, smul_smul]
    exact hcf t ht t' ht' hne _ hchord

/-- **At `lam = 1` the family is the arc.** -/
theorem straighteningFamily_one (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) :
    straighteningFamily c v Λ 1 = c := by
  funext t
  simp [straighteningFamily]

/-- **At `lam = 0` the family is the straight segment** in direction `v` starting at `c 0`. -/
theorem straighteningFamily_zero (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) :
    straighteningFamily c v Λ 0 = fun t => c 0 + (Λ * t) • v := by
  funext t
  simp [straighteningFamily]

/-- **Smoothness of the family.**  If the arc is `C^∞` then so is `(lam, t) ↦ Φ lam t`. -/
theorem contDiff_straighteningFamily {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => straighteningFamily c v Λ p.1 p.2) := by
  unfold straighteningFamily
  fun_prop

/-- **The cheap source of a chord-free direction.**  If the image of the arc lies in a linear subspace
`U` and `v ∉ U`, then `v` is chord-free for the arc (provided the arc is injective, so that its
chords are nonzero).  In particular any arc whose image is contained in a proper linear subspace of
`ℝ^m` — e.g. a planar arc — can be straightened by `straighteningFamily_injOn`, with any `v` outside
that subspace. -/
theorem chordFree_of_image_subset_subspace {U : Submodule ℝ (EuclideanSpace ℝ (Fin m))}
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ∉ U)
    {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t ∈ U)
    (hinj : Set.InjOn c (Set.Icc (0 : ℝ) 1)) : ChordFree c v := by
  intro t ht t' ht' hne α hcon
  have hmem : c t - c t' ∈ U := U.sub_mem (hc t ht) (hc t' ht')
  rw [hcon] at hmem
  by_cases hα : α = 0
  · rw [hα, zero_smul, sub_eq_zero] at hcon
    exact hne (hinj ht ht' hcon)
  · refine hv ?_
    have h2 : α⁻¹ • (α • v) ∈ U := U.smul_mem _ hmem
    rwa [smul_smul, inv_mul_cancel₀ hα, one_smul] at h2

/-- **The derivative of the straightening formula.** -/
theorem hasDerivAt_straighteningFormula {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : Differentiable ℝ c) (v : EuclideanSpace ℝ (Fin m)) (Λ lam t : ℝ) :
    HasDerivAt (fun s : ℝ => lam • c s + (1 - lam) • (c 0 + (Λ * s) • v))
      (lam • (fderiv ℝ c t 1) + (1 - lam) • (Λ • v)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (Λ * s) • v) (Λ • v) t := by
    simpa using ((hasDerivAt_id t).const_mul Λ).smul_const v
  have h2 : HasDerivAt (fun s : ℝ => c 0 + (Λ * s) • v) (Λ • v) t := h1.const_add (c 0)
  have h3 : HasDerivAt c (fderiv ℝ c t 1) t := ((hc t).hasFDerivAt).hasDerivAt
  have h4 : HasDerivAt (fun s : ℝ => lam • c s) (lam • (fderiv ℝ c t 1)) t := h3.const_smul lam
  have h5 : HasDerivAt (fun s : ℝ => (1 - lam) • (c 0 + (Λ * s) • v))
      ((1 - lam) • (Λ • v)) t := h2.const_smul (1 - lam)
  have h6 := h4.add h5
  have hfun : (fun s : ℝ => lam • c s + (1 - lam) • (c 0 + (Λ * s) • v))
      = (fun s : ℝ => lam • c s) + (fun s : ℝ => (1 - lam) • (c 0 + (Λ * s) • v)) := by
    funext s
    rfl
  rw [← hfun] at h6
  exact h6

/-- **The derivative of the straightening family in `t`.**  It is the convex combination of the
arc's tangent vector and the constant vector `Λ • v` — this is what shows that every member is again
a *regular* arc once the tangents of the original arc avoid the line `ℝ v`. -/
theorem fderiv_straighteningFamily_apply_one {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : Differentiable ℝ c) (v : EuclideanSpace ℝ (Fin m)) (Λ lam t : ℝ) :
    fderiv ℝ (straighteningFamily c v Λ lam) t 1
      = lam • (fderiv ℝ c t 1) + ((1 - lam) * Λ) • v := by
  have hbridge : straighteningFamily c v Λ lam
      = fun s : ℝ => lam • c s + (1 - lam) • (c 0 + (Λ * s) • v) := rfl
  rw [hbridge, (hasDerivAt_straighteningFormula hc v Λ lam t).hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_smul]

/-- **The straightening family consists of *regular* arcs.**  If no tangent of the arc is parallel to
`v`, the arc is regular and `Λ ≠ 0`, then every member `Φ lam` has non-vanishing derivative on
`[0,1]`.  This is exactly the `himm` hypothesis of `CutPush/ambientIsotopy_of_arcFamily`, so the
straightening family feeds the (reviewed, filed) isotopy-extension statement for arcs. -/
theorem straighteningFamily_fderiv_ne_zero {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : Differentiable ℝ c) {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) {Λ : ℝ} (hΛ : Λ ≠ 0)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ c t 1 ≠ 0)
    (hpar : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ μ : ℝ, fderiv ℝ c t 1 ≠ μ • v) :
    ∀ lam : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (straighteningFamily c v Λ lam) t 1 ≠ 0 := by
  intro lam t ht hzero
  rw [fderiv_straighteningFamily_apply_one hc v Λ lam t] at hzero
  by_cases hl : lam = 0
  · subst hl
    simp only [zero_smul, zero_add, sub_zero, one_mul] at hzero
    exact hΛ ((smul_eq_zero.mp hzero).resolve_right hv)
  · have h2 : lam • (fderiv ℝ c t 1) = (-((1 - lam) * Λ)) • v := by
      have h3 : lam • (fderiv ℝ c t 1) = -(((1 - lam) * Λ) • v) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hzero
      rw [h3, ← neg_smul]
    have h4 : fderiv ℝ c t 1 = (lam⁻¹ * (-((1 - lam) * Λ))) • v := by
      have h5 : fderiv ℝ c t 1 = lam⁻¹ • (lam • (fderiv ℝ c t 1)) := by
        rw [smul_smul, inv_mul_cancel₀ hl, one_smul]
      rw [h5, h2, smul_smul]
    exact hpar t ht _ h4

end Work.Whitney.CutPush
