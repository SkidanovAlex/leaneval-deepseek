import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `secondOrderRem`

**The requested statement is false as written.**  The requested lemma is

```
theorem secondOrderRem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {p : E} (hp : ContDiffAt ℝ 2 f p) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - (fderiv ℝ f p) ξ - (1 / 2) • ((fderiv ℝ (fderiv ℝ f) p) ξ) ξ‖
        ≤ ε * ‖ξ‖ ^ 2
```

and the problem is the literal `1 / 2`.  Nothing in the statement forces the type of
`1 / 2`, so the elaborator resolves it to `ℕ` and uses the natural-number scalar action
on `F`: `1 / 2 = 0 : ℕ` and `0 • y = 0` for `y : F`.  Hence the third term of the bound
vanishes *definitionally*, and the claim above is the *first order* Peano remainder
bound

  `‖f (p + ξ) - f p - (fderiv ℝ f p) ξ‖ ≤ ε * ‖ξ‖ ^ 2`  (for `‖ξ‖ < δ`),

which is false: take `E = F = ℝ`, `f x = x ^ 2` (a `C^∞` function, so `hp` holds),
`p = 0`, `ε = 1 / 2`.  Then the claim reads `ξ ^ 2 ≤ (1 / 2) * ξ ^ 2` for every `ξ` with
`‖ξ‖ < δ`, which fails for `ξ = δ / 2`.  (Even without computing `fderiv ℝ f 0`, adding
the claims at `ξ` and `-ξ` gives `2 * ξ ^ 2 ≤ ξ ^ 2`.)

A complete, sorry-free formal refutation — including proofs that `(1 / 2) • v = 0` for
every `v : F` and that `fun x : ℝ => x ^ 2` satisfies `ContDiffAt ℝ 2 · 0` — is in
`Submission/Work/FTS/EllSol/EllPkgAux/refute_secondOrderRem.lean` (`not_conclusion`,
`hp_poly`).

The **intended** statement — the second order Taylor (Peano remainder) theorem — is the
same statement with the scalar `1 / 2` read as a real number.  It is true and is proved
below as `secondOrderRem_real`, on top of the general helper `second_order_rem_aux`
(the proof: differentiate the second-order Taylor polynomial and use the mean value
inequality on the ball `closedBall p ‖ξ‖`; the symmetry of the second derivative is used
to identify the derivative of the quadratic term).

Note for consumers: the module currently still contains the requested statement (kept
verbatim, unproved, marked FALSE); importing it and using `secondOrderRem_real` is safe,
as the `sorry` is not in the dependency cone of `secondOrderRem_real`.
-/

namespace Work.FTS.EllSol.EllPkgAux

open Filter

/-- **Taylor's theorem with Peano remainder, to second order**, with the two derivatives
passed explicitly: if `L` is the derivative of `f` at `p`, if `Q` is the second
derivative of `f` at `p` (as a continuous linear map `E →L (E →L F)`), if `Q` is
symmetric (which it is for a `C^2` function) and if `f` is differentiable near `p`,
then

`f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ) = O (‖ξ‖ ^ 2)`.

This is the corrected form of the requested `secondOrderRem`. -/
theorem second_order_rem_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : E} {L : E →L[ℝ] F} {Q : E →L[ℝ] (E →L[ℝ] F)}
    (hL : HasFDerivAt f L p) (hQ : HasFDerivAt (fderiv ℝ f) Q p)
    (hsymm : ∀ v w : E, Q v w = Q w v)
    (hev : ∀ᶠ x in nhds p, DifferentiableAt ℝ f x) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ)‖ ≤ ε * ‖ξ‖ ^ 2 := by
  intro ε hε
  have hQε : ∀ᶠ x in nhds p, ‖fderiv ℝ f x - fderiv ℝ f p - Q (x - p)‖ ≤ ε * ‖x - p‖ :=
    hQ.isLittleO.bound hε
  rcases Metric.mem_nhds_iff.1 hQε with ⟨δ₁, hδ₁pos, hδ₁⟩
  rcases Metric.mem_nhds_iff.1 hev with ⟨δ₂, hδ₂pos, hδ₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro ξ hξ
  have hξ₁ : ‖ξ‖ < δ₁ := lt_of_lt_of_le hξ (min_le_left δ₁ δ₂)
  have hξ₂ : ‖ξ‖ < δ₂ := lt_of_lt_of_le hξ (min_le_right δ₁ δ₂)
  have hLfd : fderiv ℝ f p = L := hL.fderiv
  set K : E → F := fun x => f x - f p - L (x - p) - (1 / 2 : ℝ) • ((Q (x - p)) (x - p))
    with hK
  have hu : ∀ x : E, HasFDerivAt (fun y : E => y - p) (ContinuousLinearMap.id ℝ E) x := by
    intro x
    exact (hasFDerivAt_id (𝕜 := ℝ) x).sub_const p
  have hquad : ∀ x : E,
      HasFDerivAt (fun y : E => (Q (y - p)) (y - p)) ((2 : ℝ) • (Q (x - p))) x := by
    intro x
    have hcomp : HasFDerivAt (fun y : E => Q (y - p)) Q x := by
      have h := (ContinuousLinearMap.hasFDerivAt Q (x := x - p)).comp x (hu x)
      simpa [Function.comp_def] using h
    have h := hcomp.clm_apply (hu x)
    have hflip : Q.flip (x - p) = Q (x - p) := by
      ext v
      rw [ContinuousLinearMap.flip_apply]
      exact hsymm v (x - p)
    convert h using 1
    rw [ContinuousLinearMap.comp_id, hflip, two_smul]
  have hKderiv : ∀ x : E, DifferentiableAt ℝ f x →
      HasFDerivAt K (fderiv ℝ f x - L - Q (x - p)) x := by
    intro x hx
    have h1 : HasFDerivAt (fun y : E => f y - f p) (fderiv ℝ f x) x :=
      hx.hasFDerivAt.sub_const (f p)
    have h2 : HasFDerivAt (fun y : E => L (y - p)) L x := by
      have h := (ContinuousLinearMap.hasFDerivAt L (x := x - p)).comp x (hu x)
      simpa [Function.comp_def] using h
    have h3 : HasFDerivAt (fun y : E => (1 / 2 : ℝ) • ((Q (y - p)) (y - p)))
        ((1 / 2 : ℝ) • ((2 : ℝ) • (Q (x - p)))) x := (hquad x).const_smul (1 / 2 : ℝ)
    rw [hK]
    have hderiv : fderiv ℝ f x - L - (1 / 2 : ℝ) • ((2 : ℝ) • (Q (x - p)))
        = fderiv ℝ f x - L - Q (x - p) := by
      rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
    rw [← hderiv]
    exact (h1.sub h2).sub h3
  have hfdiff : ∀ x ∈ Metric.closedBall p ‖ξ‖, DifferentiableAt ℝ f x := by
    intro x hx
    have hxd : ‖x - p‖ < δ₂ := by
      have h2 := Metric.mem_closedBall.1 hx
      rw [dist_eq_norm] at h2
      exact lt_of_le_of_lt h2 hξ₂
    exact hδ₂ (Metric.mem_ball.2 (by rwa [dist_eq_norm]))
  have hb : ∀ x ∈ Metric.closedBall p ‖ξ‖, ‖fderiv ℝ K x‖ ≤ ε * ‖ξ‖ := by
    intro x hx
    have hxd : ‖x - p‖ < δ₁ := by
      have h2 := Metric.mem_closedBall.1 hx
      rw [dist_eq_norm] at h2
      exact lt_of_le_of_lt h2 hξ₁
    have hb₁ : ‖fderiv ℝ f x - fderiv ℝ f p - Q (x - p)‖ ≤ ε * ‖x - p‖ :=
      hδ₁ (Metric.mem_ball.2 (by rwa [dist_eq_norm]))
    rw [(hKderiv x (hfdiff x hx)).fderiv]
    calc ‖fderiv ℝ f x - L - Q (x - p)‖
        = ‖fderiv ℝ f x - fderiv ℝ f p - Q (x - p)‖ := by rw [hLfd]
      _ ≤ ε * ‖x - p‖ := hb₁
      _ ≤ ε * ‖ξ‖ := by
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            have h2 := Metric.mem_closedBall.1 hx
            rwa [dist_eq_norm] at h2
  have hKdiff : ∀ x ∈ Metric.closedBall p ‖ξ‖, DifferentiableAt ℝ K x :=
    fun x hx => (hKderiv x (hfdiff x hx)).differentiableAt
  have hpp : p ∈ Metric.closedBall p ‖ξ‖ := Metric.mem_closedBall_self (norm_nonneg ξ)
  have hpξ : p + ξ ∈ Metric.closedBall p ‖ξ‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp
  have hMVT : ‖K (p + ξ) - K p‖ ≤ (ε * ‖ξ‖) * ‖ξ‖ := by
    have h := (convex_closedBall p ‖ξ‖).norm_image_sub_le_of_norm_fderiv_le
      hKdiff hb hpp hpξ
    rwa [add_sub_cancel_left] at h
  have hKp : K p = 0 := by
    rw [hK]
    change f p - f p - L (p - p) - (1 / 2 : ℝ) • ((Q (p - p)) (p - p)) = 0
    simp
  have hKξ : K (p + ξ) = f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ) := by
    rw [hK]
    change f (p + ξ) - f p - L ((p + ξ) - p)
        - (1 / 2 : ℝ) • ((Q ((p + ξ) - p)) ((p + ξ) - p))
      = f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ)
    rw [add_sub_cancel_left]
  calc ‖f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ)‖
      = ‖K (p + ξ) - K p‖ := by rw [hKξ, hKp, sub_zero]
    _ ≤ (ε * ‖ξ‖) * ‖ξ‖ := hMVT
    _ = ε * ‖ξ‖ ^ 2 := by ring

/-- **The intended statement**: `secondOrderRem` with the scalar `1 / 2` read as a real
number.  (In the requested statement the literal `1 / 2` is read as `1 / 2 = 0 : ℕ`,
which makes the statement false; see the module comment.) -/
theorem secondOrderRem_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {p : E} (hp : ContDiffAt ℝ 2 f p) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - (fderiv ℝ f p) ξ - (1 / 2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) p) ξ) ξ‖
        ≤ ε * ‖ξ‖ ^ 2 := by
  refine second_order_rem_aux (L := fderiv ℝ f p)
    (Q := fderiv ℝ (fderiv ℝ f) p) ?_ ?_ ?_ ?_
  · exact (hp.differentiableAt (by simp)).hasFDerivAt
  · exact (ContDiffAt.differentiableAt (hp.fderiv_right (m := 1) (by norm_num))
      (by simp)).hasFDerivAt
  · intro v w
    exact hp.isSymmSndFDerivAt (by simp) v w
  · exact (hp.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)

/-- **The statement exactly as requested.**  It is *false*: the literal `1 / 2` is
elaborated with the natural-number scalar action (`1 / 2 = 0 : ℕ`), so the third term
vanishes and the claim is a first order Peano bound, which fails for `f x = x ^ 2`,
`p = 0`, `ε = 1 / 2`.  See `Submission/Work/FTS/EllSol/EllPkgAux/refute_secondOrderRem.lean`
for the formal refutation, and `secondOrderRem_real` just above for the corrected
statement. -/
theorem secondOrderRem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {p : E} (hp : ContDiffAt ℝ 2 f p) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - (fderiv ℝ f p) ξ - (1 / 2) • ((fderiv ℝ (fderiv ℝ f) p) ξ) ξ‖
        ≤ ε * ‖ξ‖ ^ 2 := by sorry

end Work.FTS.EllSol.EllPkgAux
