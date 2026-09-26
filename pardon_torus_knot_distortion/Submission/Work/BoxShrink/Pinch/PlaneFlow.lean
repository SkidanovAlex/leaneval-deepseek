import Submission.Work.BoxShrink.Pinch.Basic

/-!
# The projected gradient field of the parameter plane

`README.md` §5 records the construction that inhabits the residual inputs of the pinch: a
`2πℤ²`-periodic field of the parameter plane whose flow raises the level of the pull-back `G` of the
plane coordinate off the level `0` while keeping the pull-back `B` of the box norm *exactly*
constant (so that the flow cannot leave the box).

The field is

  `W := PG / |PG|²`,  `PG := ∇G - (⟨∇B, ∇G⟩ / |∇B|²) ∇B`,

the projection of `∇G` onto the level sets of `B`, renormalised so that `⟨∇G, W⟩ = 1`.  The two
algebraic identities that make it work are proved here in `ℝ²` (the parameter plane carries the
product norm, so the "gradient" is the pair of coordinate derivatives, exactly as in
`Work.Smooth.Morse.partialD₁`/`partialD₂`):

* `dot_projField_self` : `⟨u, W⟩ = 1`  — the flow raises `G` at unit speed;
* `dot_projField_base` : `⟨v, W⟩ = 0`  — the flow preserves `B`.

Both need only `v ≠ 0` and the linear independence of `u` and `v` (the two transversality
hypotheses of the construction).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- The inner product of `ℝ²` (the parameter plane carries the product norm, but the *dot product*
is the Euclidean one; the construction only needs the pairing of the two coordinate derivatives). -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- **The two coordinate derivatives of a function of the parameter plane**, i.e. the gradient
pair `(∂₁F, ∂₂F)`. -/
noncomputable def grad2 (F : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ F q (1, 0), fderiv ℝ F q (0, 1))

/-- The scalar product is linear in its second argument. -/
theorem dot_smul (a : ℝ) (u v : ℝ × ℝ) : dot u (a • v) = a * dot u v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **The projection of `u` onto the orthogonal complement of `v`** (before renormalisation). -/
noncomputable def projPt (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 - (dot v u / dot v v) * v.1, u.2 - (dot v u / dot v v) * v.2)

/-- **The projected field**: `projPt`, renormalised so that the pairing with `u` becomes `1`. -/
noncomputable def projField (u v : ℝ × ℝ) : ℝ × ℝ :=
  ((dot u u - dot v u ^ 2 / dot v v)⁻¹) • projPt u v

/-- The squared norm of the projected vector. -/
theorem dot_projPt_self (u v : ℝ × ℝ) (hv : dot v v ≠ 0) :
    dot u (projPt u v) = dot u u - dot v u ^ 2 / dot v v := by
  have hv' : v.1 ^ 2 + v.2 ^ 2 ≠ 0 := by simpa only [dot, pow_two] using hv
  simp only [projPt, dot]
  field_simp
  ring

/-- **The projected vector is orthogonal to `v`**: the flow preserves `B`. -/
theorem dot_projPt_base (u v : ℝ × ℝ) (hv : dot v v ≠ 0) : dot v (projPt u v) = 0 := by
  have hv' : v.1 ^ 2 + v.2 ^ 2 ≠ 0 := by simpa only [dot, pow_two] using hv
  simp only [projPt, dot]
  field_simp
  ring

/-- **The flow raises the level of `G` at unit speed**: `⟨u, W⟩ = 1` where `W = projField u v` and
`u = ∇G`, `v = ∇B`.  Only the two transversality hypotheses are needed: `∇B ≠ 0` and `∇G`, `∇B`
linearly independent. -/
theorem dot_projField_self {u v : ℝ × ℝ} (hv : dot v v ≠ 0)
    (hli : dot u u - dot v u ^ 2 / dot v v ≠ 0) : dot u (projField u v) = 1 := by
  rw [projField, dot_smul, dot_projPt_self u v hv]
  exact inv_mul_cancel₀ hli

/-- **The flow preserves `B`**: `⟨v, W⟩ = 0`. -/
theorem dot_projField_base {u v : ℝ × ℝ} (hv : dot v v ≠ 0)
    (_hli : dot u u - dot v u ^ 2 / dot v v ≠ 0) : dot v (projField u v) = 0 := by
  rw [projField, dot_smul, dot_projPt_base u v hv, mul_zero]


/-! ## The pinch field of the parameter plane -/

/-- **The field of the pinch**: the projection of the gradient of `G = planeG` onto the level sets of
`B = boxB`, renormalised.  Its flow raises `G` at unit speed and preserves `B`. -/
noncomputable def pinchField (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  projField (grad2 (planeG ψ c σ u) q) (grad2 (boxB ψ c σ) q)

/-- **The field raises the level of the plane coordinate at unit speed.** -/
theorem dot_pinchField_planeG (ψ : Submission.Diffeo) {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} {q : ℝ × ℝ}
    (hv : dot (grad2 (boxB ψ c σ) q) (grad2 (boxB ψ c σ) q) ≠ 0)
    (hli : dot (grad2 (planeG ψ c σ u) q) (grad2 (planeG ψ c σ u) q) -
        dot (grad2 (boxB ψ c σ) q) (grad2 (planeG ψ c σ u) q) ^ 2 /
          dot (grad2 (boxB ψ c σ) q) (grad2 (boxB ψ c σ) q) ≠ 0) :
    dot (grad2 (planeG ψ c σ u) q) (pinchField ψ s c σ u q) = 1 :=
  dot_projField_self hv hli

/-- **The field preserves the box norm.** -/
theorem dot_pinchField_boxB (ψ : Submission.Diffeo) {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} {q : ℝ × ℝ}
    (hv : dot (grad2 (boxB ψ c σ) q) (grad2 (boxB ψ c σ) q) ≠ 0)
    (hli : dot (grad2 (planeG ψ c σ u) q) (grad2 (planeG ψ c σ u) q) -
        dot (grad2 (boxB ψ c σ) q) (grad2 (planeG ψ c σ u) q) ^ 2 /
          dot (grad2 (boxB ψ c σ) q) (grad2 (boxB ψ c σ) q) ≠ 0) :
    dot (grad2 (boxB ψ c σ) q) (pinchField ψ s c σ u q) = 0 :=
  dot_projField_base hv hli


/-! ## Periodicity of the field

The field must be `2πℤ²`-periodic for its flow to descend to the torus.  The key point is that
`fderiv` of a function invariant under a translation is itself invariant (including at the points
where the function is *not* differentiable, where `fderiv` is the junk value `0`). -/

/-- **The derivative of a function invariant under a translation is invariant under it.** -/
theorem fderiv_periodic_shift {G : ℝ × ℝ → ℝ} {c : ℝ × ℝ} (h : ∀ q : ℝ × ℝ, G (q + c) = G q)
    (q : ℝ × ℝ) : fderiv ℝ G (q + c) = fderiv ℝ G q := by
  by_cases hd : DifferentiableAt ℝ G (q + c)
  · have key := fderiv_comp (𝕜 := ℝ) (x := q) (f := fun r : ℝ × ℝ => r + c) (g := G) hd
      (by fun_prop : DifferentiableAt ℝ (fun r : ℝ × ℝ => r + c) q)
    have hcomp : (G ∘ (fun r : ℝ × ℝ => r + c)) = G := funext h
    have hid : fderiv ℝ (fun r : ℝ × ℝ => r) q = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
      simpa using fderiv_id (𝕜 := ℝ) (x := q)
    rw [hcomp, fderiv_add_const, hid, ContinuousLinearMap.comp_id] at key
    exact key.symm
  · have h1 : fderiv ℝ G (q + c) = 0 := fderiv_zero_of_not_differentiableAt hd
    have h2 : fderiv ℝ G q = 0 := by
      refine fderiv_zero_of_not_differentiableAt (fun hq => hd ?_)
      have hshift : (fun r : ℝ × ℝ => G (r - c)) = G := by
        funext r
        have := h (r - c)
        simpa using this.symm
      have hq' : DifferentiableAt ℝ G ((q + c) - c) := by
        rw [add_sub_cancel_right]
        exact hq
      have hdiff : DifferentiableAt ℝ (fun r : ℝ × ℝ => G (r - c)) (q + c) :=
        hq'.comp (q + c) (by fun_prop)
      rwa [hshift] at hdiff
    rw [h1, h2]

/-- The two coordinate derivatives of a function invariant under a translation are invariant. -/
theorem grad2_period {F : ℝ × ℝ → ℝ} {c : ℝ × ℝ} (h : ∀ q : ℝ × ℝ, F (q + c) = F q)
    (q : ℝ × ℝ) : grad2 F (q + c) = grad2 F q := by
  simp only [grad2, fderiv_periodic_shift h q]

/-- **The pinch field is `2πℤ²`-periodic**, so its flow descends to the torus. -/
theorem pinchField_period (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (p : ℝ × ℝ) (k l : ℤ) :
    pinchField ψ s c σ u (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
      pinchField ψ s c σ u p := by
  set cc : ℝ × ℝ := ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) with hcc
  have hpt : (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) = p + cc := by
    ext <;> simp [hcc]
  have hG : ∀ q : ℝ × ℝ, planeG ψ c σ u (q + cc) = planeG ψ c σ u q := by
    intro q
    have hq : q + cc = (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) := by
      ext <;> simp [hcc]
    rw [hq, planeG_period]
  have hB : ∀ q : ℝ × ℝ, boxB ψ c σ (q + cc) = boxB ψ c σ q := by
    intro q
    have hq : q + cc = (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) := by
      ext <;> simp [hcc]
    rw [hq, boxB_period]
  rw [hpt, pinchField, pinchField, grad2_period hG p, grad2_period hB p]

end

end Work.BoxShrink.Pinch
