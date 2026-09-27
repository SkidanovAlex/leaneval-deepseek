import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.Interfaces

namespace Work.Drive

/-! # Guidance (parent agent `orderSplit_chains`) — muOrd_injective_unordered

The configuration map `muOrd γ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ`,
`(x,y) ↦ ((γ x + γ y)/2, dirC (γ x - γ y), eucNorm (γ x - γ y))`, is the piecewise formula of the
paper's map `μ` on unordered pairs of points of the circle.  Its image `M` is the configuration Möbius
strip; the paper observes (proof of Thm 1) that `μ` is injective on unordered pairs, because two chords
of the plane with the same midpoint, the same length and the same *unoriented* direction are the same
chord.  This statement records exactly that, with the two orderings of each pair identified.

Proof.  Decompose `h` into its three coordinates (`muOrd` is a nested product; use `Prod.ext` and
`congrArg`):

* `(γ x + γ y)/2 = (γ x' + γ y')/2`, i.e. `γ x + γ y = γ x' + γ y'`;
* `eucNorm (γ x - γ y) = eucNorm (γ x' - γ y')`;
* `dirC (γ x - γ y) = dirC (γ x' - γ y')`.

The third plus the second give `w = v ∨ w = -v` for `v = ⟨(γ x - γ y).1, (γ x - γ y).2⟩` and
`w = ⟨(γ x' - γ y').1, (γ x' - γ y').2⟩`: the equality in `ℝ/ℤ` says `arg w - arg v ∈ π ℤ` (compare
`AddCircle.coe_eq_zero_iff`, or reuse `Submission.Collision.exists_angle_of_dir_eq`, which already
extracts the sign ambiguity from a `dirC` equality), and equal norms then give `w = ± v`.  In the `+`
case the midpoint equality gives `γ x' = γ x` and `γ y' = γ y`; in the `-` case it gives `γ x' = γ y`
and `γ y' = γ x`.  Conclude with `hγ.isEmbedding.injective`.

The degenerate case `γ x = γ y` is covered by the same computation: then `eucNorm v = 0` forces
`eucNorm w = 0`, and the midpoint equality gives `γ x' = γ y' = γ x`, so `x = y = x' = y'` (via
`Geometry.eucNorm_eq_zero`).  Note `hxy` is deliberately *not* assumed: the statement is also used for
degenerate chords, where it says that a configuration of length `0` determines its point of `γ`.

Only injectivity of `γ` is used; having `hγ` in the statement is a matter of convenience, since that is
what callers have at hand.  `Submission.Work.Drive.muOrd_swap` (in `OrderBase`) is the companion fact
that the map takes the same value on `(x,y)` and `(y,x)`.-/

/-- Two `ℝ × ℝ`-valued equations `a + b = c + d` and `a - b = c - d` force `a = c` and `b = d`
(the linear change of coordinates `(a,b) ↦ (a + b, a - b)` is injective). -/
lemma muOrd_add_sub_inj {a b c d : ℝ × ℝ} (h1 : a + b = c + d) (h2 : a - b = c - d) :
    a = c ∧ b = d := by
  have h11 : a.1 + b.1 = c.1 + d.1 := by simpa using congrArg Prod.fst h1
  have h12 : a.2 + b.2 = c.2 + d.2 := by simpa using congrArg Prod.snd h1
  have h21 : a.1 - b.1 = c.1 - d.1 := by simpa using congrArg Prod.fst h2
  have h22 : a.2 - b.2 = c.2 - d.2 := by simpa using congrArg Prod.snd h2
  have ha1 : a.1 = c.1 := by linarith
  have ha2 : a.2 = c.2 := by linarith
  have hb1 : b.1 = d.1 := by linarith
  have hb2 : b.2 = d.2 := by linarith
  exact ⟨Prod.ext ha1 ha2, Prod.ext hb1 hb2⟩

/-- Halving (division by the scalar `2` of the product ring `ℝ × ℝ`) is injective. -/
lemma muOrd_halve_inj {a b : ℝ × ℝ} (h : a / 2 = b / 2) : a = b := by
  have h1 : a.1 / 2 = b.1 / 2 := by simpa using congrArg Prod.fst h
  have h2 : a.2 / 2 = b.2 / 2 := by simpa using congrArg Prod.snd h
  exact Prod.ext (by linarith) (by linarith)

open Manifold in
open scoped Manifold ContDiff in
/-- Two chords with the same configuration are the same unordered pair of points of `γ`. -/
theorem muOrd_injective_unordered {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {x y x' y' : Circle}
    (h : Submission.Configuration.muOrd γ (x, y) = Submission.Configuration.muOrd γ (x', y')) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  -- Decompose the equality of configurations into its three coordinates.
  have hmid : (γ x + γ y) / 2 = (γ x' + γ y') / 2 := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.1) h
    simpa [Submission.Configuration.muOrd] using this
  have hdir : Submission.Collision.dirC (γ x - γ y) =
      Submission.Collision.dirC (γ x' - γ y') := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.2.1) h
    simpa [Submission.Configuration.muOrd] using this
  have hlen : Submission.Geometry.eucNorm (γ x - γ y) =
      Submission.Geometry.eucNorm (γ x' - γ y') := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.2.2) h
    simpa [Submission.Configuration.muOrd] using this
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  -- `γ x + γ y = γ x' + γ y'`
  have hsum : γ x + γ y = γ x' + γ y' := muOrd_halve_inj hmid
  -- The two difference vectors have equal Euclidean norm and equal doubled direction, hence
  -- agree up to sign.
  have hn : ‖(⟨(γ x - γ y).1, (γ x - γ y).2⟩ : ℂ)‖ =
      ‖(⟨(γ x' - γ y').1, (γ x' - γ y').2⟩ : ℂ)‖ := by
    rw [Submission.Collision.normC_eq_eucNorm, Submission.Collision.normC_eq_eucNorm, hlen]
  have hdir' : Submission.Collision.dirC (γ x' - γ y') =
      Submission.Collision.dirC (γ x - γ y) + ((0 / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
    simp [hdir]
  obtain ⟨φ, hwφ, hvφ⟩ := Submission.Collision.exists_angle_of_dir_eq
    (v := γ x - γ y) (w := γ x' - γ y') hn hdir'
  rcases hvφ with hvφ | hvφ
  · -- `γ x - γ y = γ x' - γ y'`: the chords are equal with the same orientation.
    have hsub : γ x - γ y = γ x' - γ y' := by
      rw [hvφ, hwφ]; simp only [zero_div, sub_zero]
    obtain ⟨hx, hy⟩ := muOrd_add_sub_inj hsum hsub
    exact Or.inl ⟨hinj hx, hinj hy⟩
  · -- `-(γ x - γ y) = γ x' - γ y'`: the chords are equal with opposite orientations, so the
    -- endpoints are swapped.
    have hneg : -(γ x - γ y) = γ x' - γ y' := by
      rw [hvφ, hwφ]; simp only [zero_div, sub_zero]
    have hsub : γ x' - γ y' = γ y - γ x := by rw [← hneg]; abel
    have hsum' : γ x' + γ y' = γ y + γ x := hsum.symm.trans (add_comm (γ x) (γ y))
    obtain ⟨hx, hy⟩ := muOrd_add_sub_inj hsum' hsub
    exact Or.inr ⟨(hinj hy).symm, (hinj hx).symm⟩

end Work.Drive
