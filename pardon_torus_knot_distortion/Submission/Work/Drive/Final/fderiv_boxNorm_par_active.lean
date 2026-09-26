import Mathlib
import Submission.Work.Drive.Mono.BoxGenE

/-!
# The derivative of the box norm at an active face

Let `F = ψ(F_standard)` be the smooth torus of the challenge, parametrised by
`par ψ : ℝ × ℝ → ℝ³`, and let `boxNorm c σ` be Pardon's box norm centred at `c` with coordinate
permutation `σ` (`Submission.boxNorm`, the size parameter of the box `PBox`).

At a point `p` of the parameter plane at which the `σ i`-th box face is **active** — i.e. the
`σ i`-th coordinate of `par ψ p` sits exactly on the face
`|y (σ i) - c (σ i)| = boxSide i * s` (with sign `ε = ±1`) while all other coordinates are strictly
inside the box of size `s` — the box norm reads, near `p`, as the signed `σ i`-th face alone:

`boxNorm c σ (par ψ q) = (ε / boxSide i) * ((par ψ q) (σ i) - c (σ i))`  near `q = p`.

Differentiating gives `fderiv_boxNorm_par_active`: the differential of the pulled-back box norm is
`ε / boxSide i` times the differential of the `σ i`-th coordinate.

## Main results

* `par_coord_continuous`, `par_coord_differentiableAt` — the `σ i`-coordinate of `par ψ` is
  continuous / differentiable (the parametrisation is `C^∞`);
* `par_faceNorm_continuous` — the pulled-back face norm `faceNorm c σ j ∘ par ψ` is continuous;
* `faceNorm_eq_of_signed_coord` — the `i`-th face norm at a signed face point equals the level `s`;
* `eventually_boxNorm_eq_active_face` — near `p` the box norm is the active signed face;
* `fderiv_boxNorm_par_active` — the derivative identity.
-/

open LeanEval.KnotTheory.PardonDistortion
open Filter
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- The `σ i`-th coordinate of the parametrisation `par ψ` is continuous. -/
lemma par_coord_continuous (ψ : Submission.Diffeo) (i : Fin 3) :
    Continuous (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) i) := by
  have h : Continuous (Work.BoxShrink.Pinch.par ψ) :=
    (Work.BoxShrink.Pinch.par_contDiff ψ).continuous
  have h2 : Continuous (fun q : ℝ × ℝ =>
      (EuclideanSpace.proj (𝕜 := ℝ) i) (Work.BoxShrink.Pinch.par ψ q)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp h
  convert h2 using 2 with q
  simp

/-- The `σ i`-th coordinate of the parametrisation `par ψ` is differentiable. -/
lemma par_coord_differentiableAt (ψ : Submission.Diffeo) (i : Fin 3) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) i) p := by
  have h : Differentiable ℝ (Work.BoxShrink.Pinch.par ψ) :=
    (Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)
  have h2 : HasFDerivAt (fun q : ℝ × ℝ =>
      (EuclideanSpace.proj (𝕜 := ℝ) i) (Work.BoxShrink.Pinch.par ψ q))
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p)) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp p ((h.differentiableAt).hasFDerivAt)
  have heq : (fun q : ℝ × ℝ => (EuclideanSpace.proj (𝕜 := ℝ) i) (Work.BoxShrink.Pinch.par ψ q))
      = fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) i := by
    funext q; simp
  rw [heq] at h2
  exact h2.differentiableAt

/-- The pulled-back `j`-th face norm `faceNorm c σ j ∘ par ψ` is continuous. -/
lemma par_faceNorm_continuous (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (j : Fin 3) :
    Continuous (fun q : ℝ × ℝ =>
      Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ q)) := by
  have h := par_coord_continuous ψ (σ j)
  have heq : (fun q : ℝ × ℝ =>
        Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ q))
      = fun q : ℝ × ℝ =>
          |(Work.BoxShrink.Pinch.par ψ q) (σ j) - c (σ j)| / Submission.boxSide j := by
    funext q; rw [Work.Smooth.BoxGeneric.faceNorm_apply]
  rw [heq]
  exact ((h.sub continuous_const).abs).div_const _

/-- **The `i`-th face norm at a signed face point.**  If the `σ i`-th coordinate of `z` sits on the
face with sign `ε = ± 1` and level `s > 0`, then the corresponding face norm is exactly `s`. -/
lemma faceNorm_eq_of_signed_coord {c : R3} {σ : Equiv.Perm (Fin 3)} {i : Fin 3} {ε s : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hs : 0 < s) {z : R3}
    (hi : z (σ i) - c (σ i) = ε * (Submission.boxSide i * s)) :
    Work.Smooth.BoxGeneric.faceNorm c σ i z = s := by
  have hb : 0 < Submission.boxSide i := Submission.boxSide_pos i
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  rw [Work.Smooth.BoxGeneric.faceNorm_apply, hi, abs_mul, hεabs, one_mul,
    abs_of_pos (mul_pos hb hs)]
  exact mul_div_cancel_left₀ _ (ne_of_gt hb)

/-- **The box norm is, near an active-face point, the active signed face itself.** -/
lemma eventually_boxNorm_eq_active_face (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) {i : Fin 3} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hs : 0 < s)
    {p : ℝ × ℝ}
    (hi : (Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i) = ε * (Submission.boxSide i * s))
    (hj : ∀ j : Fin 3, j ≠ i →
      |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| < Submission.boxSide j * s) :
    ∀ᶠ q in 𝓝 p, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)
      = ε / Submission.boxSide i * ((Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i)) := by
  have hbpos : 0 < Submission.boxSide i := Submission.boxSide_pos i
  have hfi : Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ p) = s :=
    faceNorm_eq_of_signed_coord hε hs hi
  -- the sign of the active coordinate is locally constant
  have hcont_sign : Continuous (fun q : ℝ × ℝ =>
      ε * ((Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i))) :=
    continuous_const.mul ((par_coord_continuous ψ (σ i)).sub continuous_const)
  have hsign : ∀ᶠ q in 𝓝 p, 0 < ε * ((Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i)) := by
    have hpos : 0 < ε * ((Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i)) := by
      rw [hi]
      have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
      have hkey : ε * (ε * (Submission.boxSide i * s)) = Submission.boxSide i * s := by
        rw [← mul_assoc, hε2, one_mul]
      rw [hkey]; exact mul_pos hbpos hs
    exact (hcont_sign.isOpen_preimage _ isOpen_Ioi).mem_nhds hpos
  have hface : ∀ᶠ q in 𝓝 p, Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q)
      = ε / Submission.boxSide i * ((Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i)) := by
    filter_upwards [hsign] with q hq
    rw [Work.Smooth.BoxGeneric.faceNorm_apply]
    have habs : |(Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i)|
        = ε * ((Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i)) := by
      rcases hε with h | h
      · rw [h] at hq ⊢; rw [abs_of_pos (by linarith)]; ring
      · rw [h] at hq ⊢; rw [abs_of_neg (by linarith)]; ring
    rw [habs]; ring
  -- the other faces are strictly dominated near `p`
  have hle : ∀ᶠ q in 𝓝 p, ∀ j : Fin 3,
      Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ q)
        ≤ Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q) := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · subst hji; filter_upwards with q; exact le_rfl
    · have hcont : Continuous (fun q : ℝ × ℝ =>
          Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ q)
          - Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q)) :=
        (par_faceNorm_continuous ψ c σ j).sub (par_faceNorm_continuous ψ c σ i)
      have hlt0 : (Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ p)
          - Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ p)) < 0 := by
        have hfjs : Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ p) < s := by
          rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_lt_iff₀ (Submission.boxSide_pos j)]
          rw [mul_comm s (Submission.boxSide j)]
          exact hj j hji
        linarith
      filter_upwards [(hcont.isOpen_preimage _ isOpen_Iio).mem_nhds hlt0] with q hq
      exact le_of_lt (sub_neg.mp hq)
  filter_upwards [hle, hface] with q hleq hfeq
  rw [← hfeq]
  refine le_antisymm ?_ (Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i _)
  rw [Work.Smooth.BoxGeneric.boxNorm_eq_max_faceNorm]
  exact max_le (max_le (hleq 0) (hleq 1)) (hleq 2)

theorem fderiv_boxNorm_par_active (ψ : Submission.Diffeo) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (s : ℝ) {i : Fin 3} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hs : 0 < s) {p : ℝ × ℝ}
    (hi : (Work.BoxShrink.Pinch.par ψ p) (σ i) - c (σ i) = ε * (Submission.boxSide i * s))
    (hj : ∀ j : Fin 3, j ≠ i →
      |(Work.BoxShrink.Pinch.par ψ p) (σ j) - c (σ j)| < Submission.boxSide j * s) :
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p
      = (ε / Submission.boxSide i) •
        fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p := by
  have hbox := eventually_boxNorm_eq_active_face ψ c σ s hε hs hi hj
  have h1 : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p
      = fderiv ℝ (fun q : ℝ × ℝ => ε / Submission.boxSide i *
          ((Work.BoxShrink.Pinch.par ψ q) (σ i) - c (σ i))) p :=
    Filter.EventuallyEq.fderiv_eq hbox
  rw [h1]
  rw [fderiv_const_mul ((par_coord_differentiableAt ψ (σ i) p).sub_const (c (σ i)))
    (ε / Submission.boxSide i)]
  rw [fderiv_sub_const (f := fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) (c (σ i))]

end

end Work.Drive.Final
