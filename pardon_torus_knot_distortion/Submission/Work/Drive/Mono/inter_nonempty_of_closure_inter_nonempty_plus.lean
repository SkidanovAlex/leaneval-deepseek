import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Topology.SphereSlicing.convex_PBox

/-!
# From the two closed halves to their common open point

Given a convex set `A` (here Pardon's open box `Submission.PBox s c σ`), a vector `v`, a continuous
linear functional `ℓ` and two levels `k`, `lam`, this file proves that the two open pieces

* `A ∩ {ℓ > lam}` and
* `A ∩ {⟪v,·⟫ > k}`

really do meet as soon as their closures meet — provided the *seam* hypothesis

> every point of `closure A` on which both levels are attained exactly (`⟪v,y⟫ = k`, `ℓ y = lam`)
> can be lifted to a point of `A` which is still on the level `⟪v,·⟫ = k` but strictly above `lam`

is available.  The seam hypothesis is what rules out the degenerate configuration in which the two
boundaries `{⟪v,·⟫ = k}` and `{ℓ = lam}` cross inside the closed box: without it the closures of the
two pieces can meet at a point of `closure A` which is not in `A`, while the pieces themselves stay
disjoint.

The proof is pointwise.  Membership in `closure (A ∩ {ℓ > lam})` forces `lam ≤ ℓ p`, membership in
`closure (A ∩ {⟪v,·⟫ > k})` forces `k ≤ ⟪v,p⟫`.  If `k < ⟪v,p⟫`, openness of `{⟪v,·⟫ > k}` and the
first closure turn a nearby point of `A ∩ {ℓ > lam}` into a point of both pieces; symmetrically for
`lam < ℓ p`.  There remains the case `⟪v,p⟫ = k`, `ℓ p = lam`, where the seam hypothesis produces
`z ∈ A` with `⟪v,z⟫ = k` and `ℓ z > lam`; a point `a ∈ A ∩ {⟪v,·⟫ > k}` (which exists because the
second closure is nonempty) then gives, by convexity of `A`, the point `(1-t) z + t a` of `A` which
is strictly on both sides for `t > 0` small.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

/-- **The abstract point-set core.**  For a convex `A`, a vector `v`, a continuous linear functional
`ℓ` and levels `k`, `lam`: the seam hypothesis together with the meeting of the closures of the two
open pieces forces the two open pieces themselves to meet. -/
theorem inter_nonempty_aux {A : Set R3} (hconv : Convex ℝ A)
    {v : R3} {ℓ : R3 →L[ℝ] ℝ} {k lam : ℝ}
    (hseam : (∃ y ∈ closure A, inner ℝ v y = k ∧ ℓ y = lam) →
      (∃ z ∈ A, inner ℝ v z = k ∧ lam < ℓ z))
    (hcl : (closure (A ∩ {y : R3 | lam < ℓ y}) ∩
      closure (A ∩ {y : R3 | k < inner ℝ v y})).Nonempty) :
    (A ∩ {y : R3 | lam < ℓ y} ∩ {y : R3 | k < inner ℝ v y}).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  obtain ⟨p, hp1, hp2⟩ := hcl
  have hfcont : Continuous fun y : R3 => inner ℝ v y := by fun_prop
  -- the two closed half-space bounds forced on a point of the two closures
  have hfp : k ≤ inner ℝ v p := by
    have hsub : A ∩ {y : R3 | k < inner ℝ v y} ⊆ {y : R3 | k ≤ inner ℝ v y} := by
      intro y hy
      have hy' : k < inner ℝ v y := hy.2
      exact le_of_lt hy'
    exact closure_minimal hsub (isClosed_le continuous_const hfcont) hp2
  have hgp : lam ≤ ℓ p := by
    have hsub : A ∩ {y : R3 | lam < ℓ y} ⊆ {y : R3 | lam ≤ ℓ y} := by
      intro y hy
      have hy' : lam < ℓ y := hy.2
      exact le_of_lt hy'
    exact closure_minimal hsub (isClosed_le continuous_const ℓ.continuous) hp1
  -- the contradiction hypothesis, in usable form
  have hnot : ∀ y ∈ A, lam < ℓ y → k < inner ℝ v y → False := by
    intro y hyA hyl hyh
    have hm : y ∈ A ∩ {y : R3 | lam < ℓ y} ∩ {y : R3 | k < inner ℝ v y} :=
      ⟨⟨hyA, hyl⟩, hyh⟩
    rw [hcon] at hm
    exact hm
  rcases lt_or_eq_of_le hfp with hf | hf
  · -- `k < ⟪v,p⟫`: perturb a point of `A ∩ {ℓ > lam}` near `p`
    have hU : {y : R3 | k < inner ℝ v y} ∈ nhds p :=
      (isOpen_lt continuous_const hfcont).mem_nhds hf
    obtain ⟨q, hqU, hqAL⟩ := mem_closure_iff_nhds.mp hp1 _ hU
    exact hnot q hqAL.1 hqAL.2 hqU
  · rcases lt_or_eq_of_le hgp with hg | hg
    · -- `lam < ℓ p`: perturb a point of `A ∩ {⟪v,·⟫ > k}` near `p`
      have hU : {y : R3 | lam < ℓ y} ∈ nhds p :=
        (isOpen_lt continuous_const ℓ.continuous).mem_nhds hg
      obtain ⟨q, hqU, hqAH⟩ := mem_closure_iff_nhds.mp hp2 _ hU
      exact hnot q hqAH.1 hqU hqAH.2
    · -- both levels are attained at `p`: this is the seam, and `hseam` lifts it into `A`
      have hhyp : ∃ y ∈ closure A, inner ℝ v y = k ∧ ℓ y = lam :=
        ⟨p, closure_mono Set.inter_subset_left hp2, hf.symm, hg.symm⟩
      obtain ⟨z, hzA, hzF, hzG⟩ := hseam hhyp
      -- a point of `A` strictly above the level `k` exists
      have hne : (A ∩ {y : R3 | k < inner ℝ v y}).Nonempty := by
        have h := mem_closure_iff_nhds.mp hp2 Set.univ Filter.univ_mem
        simpa using h
      obtain ⟨a, haA, haF⟩ := hne
      have haF' : k < inner ℝ v a := haF
      -- a small convex combination of `z` (above `lam`) and `a` stays strictly above `lam`
      have hcont : Continuous fun t : ℝ => ℓ ((1 - t) • z + t • a) := by fun_prop
      have hgt0 : 0 < ℓ z - lam := by linarith
      obtain ⟨δ, hδpos, hδ⟩ :=
        Metric.continuousAt_iff.mp hcont.continuousAt (ℓ z - lam) hgt0
      set t : ℝ := min δ 1 / 2 with htdef
      have htpos : 0 < t := by rw [htdef]; exact div_pos (lt_min hδpos one_pos) two_pos
      have ht1 : t ≤ 1 := by
        rw [htdef]
        have h1 : min δ 1 ≤ 1 := min_le_right _ _
        linarith
      have hdist : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos htpos, htdef]
        have h1 : min δ 1 ≤ δ := min_le_left _ _
        linarith
      have hstep := hδ hdist
      have hstep' : |ℓ ((1 - t) • z + t • a) - ℓ z| < ℓ z - lam := by
        simpa [Real.dist_eq] using hstep
      have htG : lam < ℓ ((1 - t) • z + t • a) := by
        have h2 := (abs_lt.mp hstep').1
        linarith
      have hqA : (1 - t) • z + t • a ∈ A :=
        hconv hzA haA (by linarith) (le_of_lt htpos) (by ring)
      have hqF : k < inner ℝ v ((1 - t) • z + t • a) := by
        rw [inner_add_right, inner_smul_right, inner_smul_right, hzF]
        nlinarith [haF', htpos]
      exact hnot _ hqA htG hqF

theorem inter_nonempty_of_closure_inter_nonempty_plus
    {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {u h lam : ℝ} {v : LeanEval.KnotTheory.PardonDistortion.R3}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    (hseam : (∃ y ∈ closure (Submission.PBox s c σ),
        inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
      (∃ z ∈ Submission.PBox s c σ,
        inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z))
    (hcl : (closure (Submission.PBox s c σ ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | lam < ℓ y}) ∩
          closure (Submission.PBox s c σ ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 |
            inner ℝ v c + u + h < inner ℝ v y})).Nonempty) :
    (Submission.PBox s c σ ∩ {y : LeanEval.KnotTheory.PardonDistortion.R3 | lam < ℓ y} ∩
      {y : LeanEval.KnotTheory.PardonDistortion.R3 | inner ℝ v c + u + h < inner ℝ v y}).Nonempty := by
  exact inter_nonempty_aux (Work.Topology.SphereSlicing.convex_PBox s c σ) hseam hcl

end Work.Drive.Mono
