import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Vertex

/-!
# The box norm is the maximum of the three active signed faces near a vertex

At a vertex `boxVertex c σ ε s` of Pardon's box the three coordinates `param ψ p (σ i) - c (σ i)`
have signs `ε i`, and the signs of the coordinate differences are locally constant along the
smooth surface `F = ψ(standard torus)`.  Consequently, in a whole neighbourhood of the parameter
`p` over the vertex, each face norm `faceNorm c σ i` agrees with the corresponding *signed* face
`faceLin c σ i (ε i)`, and hence the box norm is the maximum of the three pulled-back signed faces.

This is the elementary local input used by `isLocalArcAt_of_vertex_tangent`: near a vertex the
box norm is the maximum of three smooth functions (with a non-degenerate corner), so the level set
is locally an arc.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.BoxGeneric.LocalSurface

/-- For a sign `ε = ±1` and a real `a`, if `ε * a` is positive then `|a| = ε * a`. -/
private lemma abs_eq_mul_of_sign (a ε : ℝ) (hε : ε = 1 ∨ ε = -1) (h : 0 < ε * a) :
    |a| = ε * a := by
  rcases hε with rfl | rfl
  · have : 0 < a := by linarith
    rw [abs_of_pos this]; ring
  · have : a < 0 := by linarith
    rw [abs_of_neg this]; ring

/-- Where the signed face `faceLin c σ i ε` is positive, it agrees with the face norm. -/
private lemma faceNorm_eq_faceLin_of_pos {c : R3} {σ : Equiv.Perm (Fin 3)} (i : Fin 3) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) {y : R3} (h : 0 < Work.Smooth.BoxGeneric.faceLin c σ i ε y) :
    Work.Smooth.BoxGeneric.faceNorm c σ i y = Work.Smooth.BoxGeneric.faceLin c σ i ε y := by
  rw [Work.Smooth.BoxGeneric.faceNorm_eq_abs_signedFace]
  rw [Work.Smooth.BoxGeneric.faceLin] at h ⊢
  exact abs_eq_mul_of_sign _ _ hε h

/-- The signed face `faceLin c σ i (ε i)` takes the value `s` at the box vertex `boxVertex c σ ε s`. -/
private lemma faceLin_boxVertex {c : R3} {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℝ}
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) (i : Fin 3) (s : ℝ) :
    Work.Smooth.BoxGeneric.faceLin c σ i (ε i) (Work.Smooth.BoxGeneric.boxVertex c σ ε s) = s := by
  have hε2 : ε i ^ 2 = 1 := by rcases hε i with h | h <;> rw [h] <;> norm_num
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  rw [Work.Smooth.BoxGeneric.faceLin, Work.Smooth.BoxGeneric.signedFace,
      Work.Smooth.BoxGeneric.boxVertex_apply]
  field_simp
  ring_nf
  rw [hε2]; ring

/-- Where the pulled-back signed face is positive, the face norm is that signed face. -/
private lemma faceNorm_param_eq_pullback {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → ℝ} (i : Fin 3) (hε : ε i = 1 ∨ ε i = -1) {q : ℝ × ℝ}
    (h : 0 < Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q) :
    Work.Smooth.BoxGeneric.faceNorm c σ i (Work.Smooth.Morse.param ψ q) =
      Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q :=
  faceNorm_eq_faceLin_of_pos i (ε i) hε h

theorem boxNorm_param_eq_max {ψ : Submission.Diffeo} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} {ε : Fin 3 → ℝ} (hs : 0 < s)
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) {p : ℝ × ℝ}
    (hp : Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s) :
    ∀ᶠ q in nhds p, Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) =
      max (max (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q)
               (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q))
          (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q) := by
  -- Near `p` each of the three pulled-back signed faces is positive: the sign of the coordinate
  -- differences does not change.
  have hpos : ∀ᶠ q in nhds p, ∀ i : Fin 3,
      0 < Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q := by
    rw [Filter.eventually_all]
    intro i
    have hcont : Continuous
        (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))) :=
      Work.Smooth.Morse.pullback_continuous ψ
        ((Work.Smooth.BoxGeneric.contDiff_faceLin c σ i (ε i)).continuous)
    have hopen : IsOpen
        ((Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))) ⁻¹'
          (Set.Ioi 0)) := isOpen_Ioi.preimage hcont
    have hpv : p ∈ (Work.Smooth.Morse.pullback ψ
        (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))) ⁻¹' (Set.Ioi 0) := by
      show 0 < Work.Smooth.BoxGeneric.faceLin c σ i (ε i) (Work.Smooth.Morse.param ψ p)
      rw [hp, faceLin_boxVertex hε i s]
      exact hs
    exact Filter.eventually_iff.mpr (hopen.mem_nhds hpv)
  -- On that neighbourhood the box norm is the maximum of the three signed faces.
  refine hpos.mono ?_
  intro q hq
  rw [Work.Smooth.BoxGeneric.boxNorm_eq_max_faceNorm,
      faceNorm_param_eq_pullback 0 (hε 0) (hq 0),
      faceNorm_param_eq_pullback 1 (hε 1) (hq 1),
      faceNorm_param_eq_pullback 2 (hε 2) (hq 2)]

end Work.Smooth.BoxGeneric.LocalSurface
