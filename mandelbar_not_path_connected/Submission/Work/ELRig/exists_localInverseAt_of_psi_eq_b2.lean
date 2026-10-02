import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit
import Submission.Work.ELRig.deriv_ne_zero_of_injOn
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Local biholomorphy of the repelling coordinate `Ψ` at a real point mapping to `b₂`

Area `Submission/Work/ELRig/` of the mandelbar project.  The rigidity argument (R-f) of
`Work.ELRig.rigidity` needs the fact that the entire repelling coordinate `Ψ` of the parabolic
flower is a *local biholomorphism* at a real point `x` with `Ψ x = b₂`, the branch point of the
tripod.  This is the statement `LocalInverseAt fl x`.

`Ψ` is not locally injective at every point (it can fail at a point whose `Ψ`-image is
precritical), so the statement is *derived*, not assumed.  The proof has two halves.

* **Reduction to the repelling half plane.**  The flower gives `Ψ` injective on a far left
  half plane `{Re w < -R₀}`, hence `deriv Ψ w ≠ 0` there.  The functional equation
  `Ψ (w+1) = F (Ψ w)` (`F = Work.EL.F c = (Tsq c)^[5]`) gives, by induction on `n`,
  `Ψ (w+n) = F^[n] (Ψ w)` and, differentiating,
  `deriv Ψ (w+n) = deriv (F^[n]) (Ψ w) * deriv Ψ w`.
  Taking `n` so large that `Re (x - n) < -R₀`, the non-vanishing of `deriv Ψ x` is reduced to
  the non-vanishing of the multiplier `deriv ((Tsq c)^[5n]) (Ψ (x-n))`.

* **The multiplier does not vanish.**  Since `Ψ (x-n)` is a preimage of `b₂` under
  `(Tsq c)^[5n]` and `b₂` is not on the critical orbit of `Tantibar c`
  (`B2Data.b2_not_postcrit`), the critical-value lemma
  `Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit` shows the multiplier is nonzero.

Finally `deriv Ψ x ≠ 0` and the analyticity of `Ψ` give the local inverse via the inverse
function theorem (`Work.ELRig.LocalInverse.exists_analytic_localInverse`), applied to a small
ball on which `Ψ` is injective (obtained from the local inverse produced by
`HasStrictDerivAt.localInverse`).
-/

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar)
open Filter Set Metric
open scoped Topology

noncomputable section

/-- `Work.EL.F c = (Tsq c)^[5]` is differentiable: it is a polynomial. -/
lemma differentiable_EL_F (c : ℂ) : Differentiable ℂ (Work.EL.F c) := by
  rw [Work.EL.F]
  have h : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
    fun_prop
  exact h.iterate 5

/-- The repelling coordinate is equivariant for the unit shift along the orbit:
`Ψ (u + n) = F^[n] (Ψ u)`, by induction from `Ψ_shift`. -/
lemma psi_add_nat {F g : ℂ → ℂ} {z₀ : ℂ} (fl : Work.EL.ParabolicFlower F g z₀)
    (n : ℕ) (u : ℂ) : fl.Ψ (u + (n : ℂ)) = F^[n] (fl.Ψ u) := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, Function.iterate_zero_apply]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, fl.Ψ_shift, ih, Function.iterate_succ_apply']

/-- The derivative of a translate: `deriv (fun v => f (v+1)) c = deriv f (c+1)`. -/
lemma deriv_comp_add_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    deriv (fun v : ℂ => f (v + 1)) c = deriv f (c + 1) := by
  have hd : HasDerivAt (fun v : ℂ => f (v + 1)) (deriv f (c + 1)) c := by
    have hcomp := (hf.differentiableAt (x := c+1)).hasDerivAt.comp c
      ((hasDerivAt_id c).add_const 1)
    have heq : (f ∘ fun x : ℂ => id x + 1) = (fun v : ℂ => f (v + 1)) := by
      funext v; simp
    rw [heq] at hcomp
    simpa using hcomp
  exact hd.deriv

/-- The derivative of the repelling coordinate at a point shifted by a natural number:
`deriv Ψ (w + n) = deriv (F^[n]) (Ψ w) * deriv Ψ w`. -/
lemma deriv_psi_add_nat {F g : ℂ → ℂ} {z₀ : ℂ} (fl : Work.EL.ParabolicFlower F g z₀)
    (hF : Differentiable ℂ F) (n : ℕ) (w : ℂ) :
    deriv fl.Ψ (w + (n : ℂ)) = deriv (F^[n]) (fl.Ψ w) * deriv fl.Ψ w := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Function.iterate_zero, deriv_id, one_mul]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc]
    have hfun : (fun v : ℂ => fl.Ψ (v + 1)) = (F ∘ fl.Ψ) := by
      funext v; exact fl.Ψ_shift v
    rw [← deriv_comp_add_one fl.Ψ_diff (w + (n : ℂ)), hfun]
    rw [deriv_comp (x := w + (n : ℂ)) (h := fl.Ψ) (h₂ := F)
          (hF.differentiableAt (x := fl.Ψ (w + (n : ℂ))))
          (fl.Ψ_diff.differentiableAt (x := w + (n : ℂ)))]
    rw [psi_add_nat fl n w, ih]
    rw [show deriv (F^[n.succ]) (fl.Ψ w)
          = deriv F (F^[n] (fl.Ψ w)) * deriv (F^[n]) (fl.Ψ w) from by
        rw [Function.iterate_succ']
        exact deriv_comp (fl.Ψ w) (hF.differentiableAt (x := F^[n] (fl.Ψ w)))
          ((hF.iterate n).differentiableAt (x := fl.Ψ w))]
    ring

/-- `Ψ` is locally biholomorphic at a real point `x` whose `Ψ`-image is the branch point
`b₂` of the tripod. -/
theorem exists_localInverseAt_of_psi_eq_b2 {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (tr : Work.EL.B2Data d.hN d.z₁) {x : ℝ} (hx : fl.Ψ (x : ℂ) = tr.b₂) :
    Work.EL.LocalInverseAt fl x := by
  -- `Ψ` is injective on a far left half plane
  obtain ⟨R₀, hR₀⟩ := fl.Ψ_inj
  -- choose `n ≥ 1` with `x - n < -R₀`, and set `w = x - n`
  obtain ⟨m, hm⟩ := exists_nat_gt (R₀ + x)
  set n : ℕ := max m 1
  have hn1 : 1 ≤ n := le_max_right m 1
  have hmn : R₀ + x < (n : ℝ) := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left m 1
    linarith
  set w : ℂ := (x : ℂ) - (n : ℂ) with hw_def
  have hwre : w.re < -R₀ := by
    rw [hw_def, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re]
    linarith
  -- injectivity on the half plane gives a non-zero derivative at `w`
  have hU : IsOpen {z : ℂ | z.re < -R₀} := isOpen_lt Complex.continuous_re continuous_const
  have hderivΨw : deriv fl.Ψ w ≠ 0 :=
    Work.ELRig.deriv_ne_zero_of_injOn fl.Ψ_diff.differentiableOn hU hR₀ hwre
  have hxw : (x : ℂ) = w + (n : ℂ) := by rw [hw_def]; ring
  -- `Ψ w` is a preimage of `b₂` under `(Tsq c)^[5n]`
  have hFn_b2 : ((Work.EL.F c)^[n]) (fl.Ψ w) = tr.b₂ := by
    rw [← psi_add_nat fl n w, ← hxw, hx]
  have hiter : ((Work.EL.F c)^[n]) = (Work.Landing.Tsq c)^[5 * n] := by
    rw [Work.EL.F]
    exact (Function.iterate_mul (Work.Landing.Tsq c) 5 n).symm
  have hb2_tsq : (Work.Landing.Tsq c)^[5 * n] (fl.Ψ w) = tr.b₂ := by
    rw [← hiter]; exact hFn_b2
  have hFn_ne : deriv ((Work.EL.F c)^[n]) (fl.Ψ w) ≠ 0 := by
    rw [hiter]
    exact Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit (Nat.mul_pos (by norm_num) hn1)
      tr.b2_not_postcrit hb2_tsq
  -- the derivative at `x` does not vanish
  have hderivx : deriv fl.Ψ (x : ℂ) ≠ 0 := by
    have hformula := deriv_psi_add_nat fl (differentiable_EL_F c) n w
    rw [← hxw] at hformula
    rw [hformula]
    exact mul_ne_zero hFn_ne hderivΨw
  -- `Ψ` is injective on a small ball around `x`
  have hinj : ∃ δ > 0, Set.InjOn fl.Ψ (Metric.ball (x : ℂ) δ) := by
    have hstrict : HasStrictDerivAt fl.Ψ (deriv fl.Ψ (x:ℂ)) (x:ℂ) :=
      (fl.Ψ_diff.analyticAt (x:ℂ)).hasStrictDerivAt
    let σ := HasStrictDerivAt.localInverse fl.Ψ (deriv fl.Ψ (x:ℂ)) (x:ℂ) hstrict hderivx
    have hleft : ∀ᶠ u in nhds (x:ℂ), σ (fl.Ψ u) = u := hstrict.eventually_left_inverse hderivx
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hleft
    refine ⟨δ, hδpos, fun a ha b hb hab => ?_⟩
    have ha' : σ (fl.Ψ a) = a := hδsub ha
    have hb' : σ (fl.Ψ b) = b := hδsub hb
    rw [← ha', hab, hb']
  -- the inverse function theorem
  obtain ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, σ, hσan, hσright, hσleft, _⟩ :=
    Work.ELRig.LocalInverse.exists_analytic_localInverse fl.Ψ_diff hinj
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, σ, ?_, ?_, ?_⟩
  · exact hσan.mono (Metric.ball_subset_ball (min_le_right _ _))
  · intro w' hw'
    exact hσleft w' (Metric.ball_subset_ball (min_le_left _ _) hw')
  · intro z hz
    exact hσright z (Metric.ball_subset_ball (min_le_right _ _) hz)

end

end Work.ELRig
